# Reusing Kraken's FFmpeg proofs in an Iris client

This repository demonstrates certificate-based reuse of independently verified native code inside a structured Iris separation-logic client. The example is a concurrent service around FFmpeg's SBR processing routine, using the original Kraken execution proofs.

**Start with [VerifiedReadyService.lean](SbrClient/Client/VerifiedReadyService.lean).** It is the final theorem that connects everything. The program and substantial Iris proofs live in its imports, especially [ReadyService.lean](SbrClient/Client/ReadyService.lean) and [Service.lean](SbrClient/Client/Service.lean).

The previous two-example experiment is preserved in [attic.zip](attic.zip), including the former MachCSL example, Git metadata, build caches, and a file-hash manifest. The working project is now the FFmpeg/Kraken example. `Kraken/` and `KrakenTactics/` contain the upstream dependency sources; `SbrClient/` contains the certificate bridge and Iris application.

**Folder guide.** The 35 modules in `SbrClient/` are organized by responsibility:

```text
SbrClient/
├── Client/   Concurrent service, checksum result, and public application theorems
├── FFmpeg/   SBR resources, native call contracts, and original-proof provider
├── Host/     Shared-memory host language, synchronization, loads/stores, and FFI
├── Machine/  Kraken execution model, instruction locality, and byte ownership
├── Logic/    Certificate-accepting weakest precondition and its soundness
└── Audit/    Axiom audits for the logic, machine, host, and completed service
```

The application uses the FFmpeg call interface and host rules; those are supported by the machine/resource bridge and certificate logic. Lean declaration names remain stable. To import the public theorem:

```lean
import SbrClient.Client.VerifiedReadyService

#check SbrClient.SbrAPI.wp_verifiedReadyService
#check SbrClient.SbrAPI.cwp_verifiedReadyService
```

**What the program does.** The example starts with an already-ready decoder and two 8,192-byte output buffers. Two worker threads repeatedly call the native routine using that shared decoder and those same buffers. Writing `N = rounds + 1`, the program is roughly:

```text
Each of two workers, N times:
    acquire decoder lock
    claim free output buffers
    call native ff_aac_sbr_apply
    release decoder lock
    publish output buffers as ready

Consumer:
    consume and acknowledge 2*N - 1 publications
    claim the final publication
    compute XOR over all 16,384 output bytes
    acquire decoder lock
    return checksum, retaining ownership of decoder and buffers
```

That last “retaining ownership” describes the logical postcondition: the runtime returns a checksum byte, while the proof gives the caller resources it can use in subsequent verification. For `rounds = 0`, each worker makes one call; the consumer acknowledges the first publication and retains the second.

**What Iris proves.** The interesting reasoning is the separation between decoder ownership and output ownership. The lock protects decoder state and call resources. The mailbox transfers the buffers between workers and consumer. A worker must obtain both before entering native code. After the call, Iris splits the returned resources: decoder state goes back into the lock, and buffers are published through the mailbox. While the consumer scans those buffers, workers cannot obtain permission to overwrite them.

You can see this directly in `wp_producerOnce` in [Service.lean](SbrClient/Client/Service.lean): acquire resources, combine them for the native call, recover them, split them, release and publish. That proof is ordinary Iris reasoning. The final consumer keeps its buffer claim, acquires the decoder lock, and returns both sets of resources to its caller. The returned protocol handles and exclusive tokens let a subsequent verified client continue or release them.

**Where the certificate enters.** `verifiedCalls` in [Provider.lean](SbrClient/FFmpeg/Provider.lean) instantiates the call interface with the actual upstream Kraken proofs. Their operational execution theorem becomes a certificate through `wp_native_run` in [Native.lean](SbrClient/Host/Native.lean). The machine/resource bridge maintains ownership at every native instruction, so other threads can interleave throughout the call.

```text
original Kraken execution theorem (Eventually over native instructions)
    → certificate_of_eventually
    → Host.wp_native_certificate
    → BinaryCert.cwp_certificate
    → compositional Iris native-call rule
    → worker / mailbox / consumer proof
```

The 165-module, 141,354-line upstream dependency closure stays behind that interface. The new synchronization and checksum proofs do not revisit its instruction proofs. `cwp` contains a certificate-acceptance branch in its guarded definition. Its proved equivalence with ordinary Iris WP allows the client to use existing Iris rules for invariants, framing and fork. The final `cwp_verifiedReadyService` theorem uses that compatibility equivalence; certificate acceptance itself happens inside the native-call rule.

**What the final theorem says.** Schematically:

```text
ready decoder ownership ∗ output buffers ∗ initial flags ∗ Ψ
    ⊢ WP service {
        checksum matches the returned buffer contents
        ∗ ownership of both buffers
        ∗ decoder and call-resource ownership
        ∗ lock/mailbox handles and exclusive tokens
        ∗ Ψ
      }
```

The checksum is tied to the very byte maps whose ownership is returned. The arbitrary Iris assertion `Ψ` is preserved across the service. `VerifiedReadyService` supplies the concrete upstream proof provider: its public theorems have no abstract `Calls` provider hypothesis.

**An easy guide to the theorem.** Read these in order; the first four explain the application without requiring a tour of the native proofs.

| File | Definitions/theorems to find | What to look for |
| --- | --- | --- |
| [VerifiedReadyService.lean](SbrClient/Client/VerifiedReadyService.lean) | `wp_verifiedReadyService`, `cwp_verifiedReadyService` | Public assumptions, preserved caller frame, and concrete provider instantiation. |
| [ReadyService.lean](SbrClient/Client/ReadyService.lean) | `readyService`, `readyResult`, `heldResult`, `wp_takeFinal`, `wp_readyService` | Actual concurrent program, invariant initialization, and final ownership handoff. |
| [Service.lean](SbrClient/Client/Service.lean) | `producerOnce`, `consumerOnce`, `wp_producerOnce` | How Iris splits, transfers and recombines decoder/buffer resources around each call. |
| [StrongOutput.lean](SbrClient/Client/StrongOutput.lean) | `checksumResult`, `wp_consumeOutputs_exact` | Exact checksum of both returned owned byte maps. |
| [Provider.lean](SbrClient/FFmpeg/Provider.lean) | `verifiedCalls` | Connection to the original Kraken proof artifacts. |
| [Calls.lean](SbrClient/FFmpeg/Calls.lean), [Native.lean](SbrClient/Host/Native.lean) | `wp_apply_owned`, `wp_native_run` | Native execution proof becomes an Iris call rule. |
| [Adapter.lean](SbrClient/Machine/Adapter.lean), [Host/Language.lean](SbrClient/Host/Language.lean) | `certificate_of_eventually`, `wp_native_certificate` | Generic certificate conversion and lifting into the concurrent host language. |
| [CertifiedWP.lean](SbrClient/Logic/CertifiedWP.lean) | `externalPre`, `cwp_certificate`, `external_adequate`, `cwp_eq_native` | Built-in certificate acceptance, soundness, and ordinary-WP compatibility. |

`Host/Lock.lean`, `Mailbox.lean`, and `Fork.lean` prove the synchronization rules. `Frame.lean` and `Ownership.lean` establish instruction-level spatial locality and the concrete Iris byte-heap interpretation. `VerifiedService.lean` retains an earlier configuration/startup variant of this same FFmpeg example; the main ready-state theorem is in `VerifiedReadyService.lean` and does not call `config_usac`.

**Reproduce the checks.** From the repository root in the prepared workspace:

```sh
make theorem   # Fast recheck of the public theorem using existing dependency caches.
make check     # Full upstream provenance/build, client rebuild, axiom and object checks.
```

The full check is also available as `python3 tools/check-project`. It checks the original source excerpts against pinned Kraken commit `b60a6f97373dbb537d0576fd40b8b7c2520b4de3`, builds the upstream dependency closure, recompiles all 35 client modules, and audits 40 theorems. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. Three upstream files have the disclosed mechanical `allSome` → `krakenAllSome` helper rename for Lean 4.35 compatibility; other reused dependency sources must match the pinned commit.

The scripts use Lean 4.35 from `lean-toolchain`, Python 3, and a Linux systemd user session for memory limits. `tools/check-iris` uses the already-built Iris/Batteries/Qq package cache at `/home/agent/iris-intrinsic-complete/.lake/packages`. To use another compatible cache:

```sh
IRIS_PACKAGE_CACHE=/path/to/compatible/.lake/packages make check
```

The Iris revision used here is `8293092f09bd32ec60640f4267e7b7cd98bfe024`. The full object check also uses the bundled ARM64-hosted x86 binutils and LLVM 21's shared library; `SBR_LLVM_LIBRARY` can override the LLVM library path. These are environment prerequisites, not an automatic fresh-machine setup. The upstream Lake default targets include other Kraken tooling; `make check` is this example's verification entry point.

Each Lean build runs through `tools/bounded-build`: builds are serialized under one lock, with an 8 GiB limit (2 GiB with `--small`) and a 24 GB system-memory-pressure stop threshold. The full checker applies these limits internally. Results are recorded in [validation.json](validation.json), with individual logs and source fingerprints under `checks/`. [manifest.json](manifest.json) records the example's scope and theorem names.

**Scope of the result.** This is a conditional library-client verification. It inherits Kraken's code-placement and external-library contracts, assumes a ready decoder, and uses modeled host glue. It proves safety and the stated result upon return; it does not establish audio correctness or termination. No complete inhabited external environment has been supplied.

The artifact under `binary/open-library/` is an open relocatable assembly of 39 exported native texts. Its external references remain unresolved. It is not the original FFmpeg executable or a closed linked image. The object checks establish export identity, instruction boundaries, mnemonics and address-size prefixes; they do not prove full operand equivalence. These boundaries are also recorded in [the object validation report](binary/open-library/validation.json).

The verified composition is the point: a large independent native proof supplies a call contract, and Iris uses that contract inside a new concurrent ownership protocol with a useful, resource-bearing result.
