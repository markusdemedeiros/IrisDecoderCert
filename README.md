# Reusing Kraken's FFmpeg proofs in an Iris client

This repository demonstrates how to reuse Kraken's native-code proofs in an Iris separation-logic client. The example is a concurrent service around FFmpeg's spectral band replication (SBR) routine. A certificate connects the existing execution proof to Iris, where the client proves synchronization, buffer ownership, and an exact output checksum.

The result is conditional verification of a mixed-language program. Native calls execute Kraken's decoded x86 instructions; host operations use an explicit shared-memory model. The theorem assumes the upstream code-placement and external-library contracts. The repository does not supply a compiled host runtime or a closed FFmpeg executable.

Start with the [public service theorem](SbrClient/Client/VerifiedReadyService.lean) to inspect its assumptions and postcondition. In the prepared workspace, enter this command from the repository root to recheck that theorem:

```sh
make theorem
```

The command uses existing dependency caches. For the required environment and full validation procedure, follow [Reproducing the checks](#reproducing-the-checks).

Use these topics to evaluate the example:

- [Service and ownership protocol](#service-and-ownership-protocol): Program behavior and the final contract
- [Native foreign function interface](#native-foreign-function-interface): CPU state, shared memory, call boundaries, and proof assumptions
- [Reused theorems and code size](#reused-theorems-and-code-size): Original FFmpeg results and reproducible source counts
- [Reading the code](#reading-the-code): Directory layout and a guide to the proof

## Service and ownership protocol

The service starts with a ready decoder and two 8,192-byte output buffers. Two producer threads share the decoder and buffers. Each producer makes `rounds + 1` native calls. A consumer reads the published buffers and returns the final checksum.

A lock protects the decoder and call resources. A mailbox transfers exclusive buffer ownership between the producers and consumer. The mailbox uses three flag values: free (`0`), ready (`1`), and busy (`2`). A successful compare-and-swap (CAS) claims the buffers by changing the expected flag to busy.

The following pseudocode shows the ownership protocol, with `N = rounds + 1`:

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

For each ordinary publication, the consumer reads all output bytes before marking the buffers free. Producers cannot claim the buffers during the scan. The final consumer keeps its buffer claim and acquires the decoder lock. For `rounds = 0`, each producer makes one call; the consumer acknowledges the first publication and retains the second.

The producer proof combines decoder and buffer ownership to satisfy the native call's precondition. After the call, Iris separates the returned resources. Decoder ownership goes back into the lock invariant, and buffer ownership passes through the mailbox invariant. The [producer and consumer definitions and proofs](SbrClient/Client/Service.lean) show each transfer.

### Final contract

The service returns a checksum byte. Its logical postcondition also gives the caller exclusive decoder and buffer ownership, together with the protocol handles needed to continue or release those resources.

The public theorem uses the Iris weakest precondition (WP). Its contract has this schematic form:

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

The assertion `Ψ` represents arbitrary caller resources preserved across the service. The checksum equals the bytewise XOR of the two buffer maps whose ownership the theorem returns. The [exact checksum proof](SbrClient/Client/OutputConsumer.lean) establishes that relation by reading each byte.

### Certificate reuse

The certificate is a pure Lean execution proof accepted by the certificate branch of `cwp`, the weakest precondition defined in this project. The proved equivalence between `cwp` and ordinary Iris WP supports composition with Iris rules for invariants, framing, and fork.

The concrete `verifiedCalls` provider supplies the original Kraken proofs. The public service theorems therefore have no abstract `Calls` provider hypothesis. The final `cwp_verifiedReadyService` theorem uses the WP equivalence; the native-call rule invokes certificate acceptance. The [certificate logic](SbrClient/Logic/CertifiedWP.lean) defines the branch and proves its soundness.

## Native foreign function interface

The foreign function interface (FFI) connects the operational semantics and ownership rules of the host and native languages. The host controller executes modeled operations. Each native execution step uses Kraken's instruction interpreter.

### CPU and memory mapping

The execution configuration contains the threads' expressions and one shared byte heap. The following table maps each component to its representation:

| Component | Representation |
| --- | --- |
| General registers, vector registers, status flags, and program counter | Thread-local `CPU` in `.native (.run c) k` |
| Stack, decoder, output buffers, and synchronization flags | Shared language state `Mem 64` |
| Fixed decoded instructions and labels | `Model.code` |
| Host computation after return | Continuation `k : CPU → Host.Expr M` |

The `CPU.pack` function combines the CPU and shared heap into Kraken's machine state:

```lean
def CPU.pack (c : CPU) (m : Mem 64) : MachineState :=
  (⟨c.regs, c.zmms, c.status, m⟩, c.pc)
```

After an instruction, `CPU.ofMachine` extracts the registers, flags, and program counter. The step rule installs the resulting `dmem` as the shared heap. The `CPU.pack_ofMachine` theorem proves that splitting and recombining a Kraken state recovers the exact state.

Both languages access the same byte addresses. An FFmpeg store changes the memory subsequently read by the consumer. The mapping requires no buffer copy or address translation. The [machine language definitions](SbrClient/Machine/Language.lean) specify the mapping and step rules.

### Call entry and return

The reusable call prepares the return slot, enters native execution, and resumes a host continuation:

```lean
def applyOnce (c : CPU) (next : Host.Expr M) : Host.Expr M :=
  Host.prepare c (.native (.run c) (fun _ => next))
```

The caller supplies `c` with the FFmpeg entry program counter and registers satisfying the upstream `ApplyCall` conditions. The caller also supplies ownership of the decoder, output buffers, return slot, and stack reserve.

The `Host.prepare` operation writes the 8-byte return address `M.halt` at the stack pointer through explicit host stores. Its proof establishes the original System V application binary interface (ABI) precondition, `CallPre`. The [call-setup proof](SbrClient/FFmpeg/CallSetup.lean) accounts for these stores and their memory ownership.

The `Step.native` rule lifts one machine step at a time. An execution step follows an `InstrOutcome` from Kraken's interpreter. Other threads can run between native instructions. The successful path has this form:

```text
native (run c) k, memory
    → native (run c') k, memory'       one native instruction
    → …
    → native (run c_return) k, memory_final   PC = M.halt
    → native (done c_return) k, memory_final
    → k c_return, memory_final
```

The `M.halt` address is a designated return boundary with an empty code lookup. Internal native calls and returns use ordinary instruction addresses. Reaching the outer boundary resumes the saved host continuation. The [host language rules](SbrClient/Host/Language.lean) define this transition and the shared-memory operations.

The generic FFI passes the returned CPU to `k`. The `applyOnce` operation discards that CPU. Each subsequent call starts from the supplied CPU template `c`, with the updated shared memory and a freshly written return slot.

Register argument setup and the transition into host control are part of the modeled interface. The proof does not cover a compiled calling stub that reconstructs `c`. The [reusable-call definition and proof](SbrClient/FFmpeg/Reusable.lean) make that boundary explicit.

### Shared memory and certificate acceptance

The upstream proof describes execution on an owned memory fragment `p`. Iris execution uses the whole shared heap `σ`. The relation `Agrees p σ` states that `σ = p.union f` for a disjoint memory fragment `f`, called the frame.

The instruction-locality theorem relates execution on the whole heap to execution on the owned fragment. Each native step preserves the frame. Other threads can change their own memory between native steps. The [instruction-locality proof](SbrClient/Machine/Frame.lean) establishes these properties for Kraken's interpreter.

Iris represents the owned fragment as exclusive ownership of its bytes. The ownership proof connects that fragment to the shared heap and updates the assertions after native writes. Fault outcomes appear explicitly as stuck execution, so the safety proof must exclude them. The [byte-ownership interpretation](SbrClient/Machine/Ownership.lean) connects the memory model to Iris.

The native execution theorem reaches the client through this proof chain:

```text
original Kraken execution theorem (Eventually over native instructions)
    → certificate_of_eventually
    → Host.wp_native_certificate
    → BinaryCert.cwp_certificate
    → compositional Iris native-call rule
    → worker / mailbox / consumer proof
```

The `wp_native_run` theorem converts the upstream execution result into a certificate and a host WP rule. At return, the FFmpeg adapter converts `CallPost` into Iris ownership of the decoder, ABI resources, output buffers, and caller resources. The producer can then transfer those resources to the lock and mailbox invariants. Native execution remains interruptible throughout the call.

For the conversion and returned resources, read the [native-run rule](SbrClient/Host/Native.lean) and [FFmpeg call rules](SbrClient/FFmpeg/Calls.lean).

### Proof assumptions and boundaries

The public theorem proves safety, preservation of the caller's frame, and the stated result if the mixed-language service returns. The theorem retains these assumptions:

- Original `SessPlaced` code placement
- Equality of the upstream code environment and `Model.code`
- Entry-register, alignment, and stack conditions
- A ready decoder carrying the inherited external-library contracts
- The empty-code return boundary required by `Model`

Host loads, stores, and CAS follow sequentially consistent interleaving rules. The development supplies neither a compiled host runtime nor a refinement to a hardware memory model. It also supplies no complete inhabited external environment or closed executable implementing every external contract.

The theorem does not establish decoded-audio correctness, fairness, or service termination. The [binary artifact checks](#binary-artifact) have a separate, limited scope.

## Reused theorems and code size

The public native theorem is `Kraken.Examples.Sbr.SessionBin.apply_top`. The local provider copies its body verbatim as `SbrClient.Upstream.apply_top` to avoid unrelated parser-proof imports. That proof uses `session_apply`, which invokes `Kraken.Examples.Sbr.ff_aac_sbr_apply_linked`.

The linked theorem covers `ff_aac_sbr_apply`, its 5 C helper routines, 12 SBR digital signal processing (DSP) routines, and 8 floating-point DSP routines. Those 26 routines retain the original placement and external-call contracts. The provider supplies both apply and configuration wrappers; the main ready-state client uses apply.

To inspect the original results, read the [public wrapper](Kraken/X64/Examples/Sbr/SessionBin/TopCalls.lean), [session theorem](Kraken/X64/Examples/Sbr/SessionBin/SApply.lean), and [linked native theorem](Kraken/X64/Examples/Sbr/Link.lean). The [local wrapper excerpts](SbrClient/FFmpeg/UpstreamCalls.lean) contain the copied declarations.

The source counts measure transitive module import closures: each root module and every local module it imports, directly or indirectly. Each file counts once per closure. FFmpeg-specific files are under `Kraken/X64/Examples/Sbr/`; other imported `Kraken/` and `KrakenTactics/` files count as framework code.

The counts are physical Lean lines of code (LOC), including comments, blank lines, instruction texts, specifications, and data tables. They exclude external Lean, Iris, Batteries, and Qq sources. They measure neither FFmpeg C source nor exact declaration-level proof dependencies.

<!-- reuse-metrics:start -->
The following table separates FFmpeg verification code from Kraken framework code for each reused module closure:

| Reused module closure | FFmpeg-specific Lean LOC | Kraken framework LOC | Total LOC |
| --- | ---: | ---: | ---: |
| Native theorem: `ff_aac_sbr_apply_linked` | 111,962 | 22,202 | 134,164 |
| Session theorem: `session_apply` | 118,615 | 22,202 | 140,817 |
| Imported provider: apply and configuration wrappers | 119,152 | 22,202 | 141,354 |

The following table counts the new glue and client code in the main theorem's import closure:

| New code needed by `VerifiedReadyService` | Modules | Lean LOC |
| --- | ---: | ---: |
| Certificate logic, machine bridge, and host semantics | 16 | 2,224 |
| FFmpeg-specific resources and call adapter | 6 | 415 |
| Iris application and public theorem | 4 | 519 |
| Total new glue and client | 26 | 3,158 |

The total excludes 227 lines of copied upstream wrapper excerpts. The optional startup variant and axiom-audit modules are also outside the main theorem's import closure.
<!-- reuse-metrics:end -->

The imported provider accounts for 165 upstream modules. The synchronization and checksum proofs use its interface without repeating the instruction proofs. The [machine-readable metrics](reuse-metrics.json) record the counts and their definitions.

To check that the tables match the source tree, enter this command:

```sh
python3 scripts/reuse-metrics.py --check
```

After changing the counted sources, refresh both the tables and metrics file with this command:

```sh
python3 scripts/reuse-metrics.py --write
```

## Reading the code

The `SbrClient/` directory contains 34 modules organized by responsibility. The application depends on the FFmpeg call interface and host rules, which depend on the machine bridge and certificate logic.

The directory layout separates those responsibilities:

```text
SbrClient/
├── Client/   Concurrent service, checksum result, and public application theorems
├── FFmpeg/   SBR resources, native call contracts, and original-proof provider
├── Host/     Shared-memory host language, synchronization, loads/stores, and FFI
├── Machine/  Kraken execution model, instruction locality, and byte ownership
├── Logic/    Certificate-accepting weakest precondition and its soundness
└── Audit/    Axiom audits
```

Read the files in the following order. The first four cover the application without requiring a review of the native instruction proofs.

| Source | Definitions and theorems | Purpose |
| --- | --- | --- |
| [Public service theorem](SbrClient/Client/VerifiedReadyService.lean) | `wp_verifiedReadyService`, `cwp_verifiedReadyService` | Assumptions, caller frame, and concrete provider |
| [Main service](SbrClient/Client/ReadyService.lean) | `readyService`, `readyResult`, `wp_takeFinal`, `wp_readyService` | Concurrent program and final ownership transfer |
| [Producer and consumer](SbrClient/Client/Service.lean) | `producerOnce`, `consumerOnce`, `wp_producerOnce` | Resource transfers around each native call |
| [Output consumer](SbrClient/Client/OutputConsumer.lean) | `checksumResult`, `wp_consumeOutputs_exact` | Exact checksum of the returned buffers |
| [Proof provider](SbrClient/FFmpeg/Provider.lean) | `verifiedCalls` | Original Kraken proofs behind the call interface |
| [FFmpeg call rules](SbrClient/FFmpeg/Calls.lean) | `wp_apply_owned`, `wp_apply` | Native proof and returned Iris resources |
| [Native-run rule](SbrClient/Host/Native.lean) | `wp_native_run` | Execution proof accepted as a host call |
| [Certificate conversion](SbrClient/Machine/Adapter.lean) | `certificate_of_eventually` | Generic conversion of Kraken execution proofs |
| [Certificate logic](SbrClient/Logic/CertifiedWP.lean) | `externalPre`, `cwp_certificate`, `external_adequate`, `cwp_eq_native` | Certificate branch, soundness, and WP equivalence |

The `Host/Lock.lean`, `Host/Mailbox.lean`, and `Host/Fork.lean` modules prove synchronization rules. The `Client/VerifiedService.lean` module retains an earlier configuration and startup variant of the same example. The main theorem uses `VerifiedReadyService` and does not call `config_usac`.

To reference the public theorems from Lean, use this import:

```lean
import SbrClient.Client.VerifiedReadyService

#check SbrClient.SbrAPI.wp_verifiedReadyService
#check SbrClient.SbrAPI.cwp_verifiedReadyService
```

The `Kraken/` and `KrakenTactics/` directories contain upstream sources. The optional local `attic.zip` archive preserves the earlier experiment, including MachCSL, Git metadata, build caches, and a file-hash manifest. The archive is not tracked in Git.

## Reproducing the checks

The project checker validates source provenance, rebuilds the example, audits theorem axioms, and checks the generated native object. The commands require the prepared workspace or an equivalent environment.

### Prerequisites

Before entering the check commands, provide these dependencies:

- Lean 4.35, as specified in `lean-toolchain`
- Python 3 and a Linux systemd user session for build memory limits
- Built Iris, Batteries, and Qq packages, with Iris revision `8293092f09bd32ec60640f4267e7b7cd98bfe024`
- The bundled ARM64-hosted x86 binutils and the LLVM 21 shared library for the object check

The `tools/check-iris` script uses the package cache at `/home/agent/iris-intrinsic-complete/.lake/packages`. Set `IRIS_PACKAGE_CACHE` to use another compatible cache. Set `SBR_LLVM_LIBRARY` to override the LLVM library path. The checker does not install these prerequisites.

### Running the checks

To validate the example in the prepared workspace, follow these steps:

1. From the repository root, enter the full check command:

   ```sh
   make check
   ```

2. Inspect the [validation report](validation.json) for the result and evidence directory. Individual logs and source fingerprints are under `checks/`.

If a check fails, inspect the log named in the failure message. Resolve the reported problem before repeating the check.

To use a different package cache, replace `/path/to/compatible/.lake/packages` with its location and enter this command:

```sh
IRIS_PACKAGE_CACHE=/path/to/compatible/.lake/packages make check
```

The `make theorem` command rechecks only the public theorem using existing dependency caches. The `python3 tools/check-project` command runs the full check directly. Use these project commands instead of the upstream Lake default targets, which include other Kraken tooling.

### Check coverage

The full check compares copied excerpts and dependency sources with pinned Kraken commit `b60a6f97373dbb537d0576fd40b8b7c2520b4de3`. It builds 165 upstream dependency modules, recompiles all 34 client modules, checks the LOC tables, and audits 40 theorems. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Three upstream files contain a mechanical `allSome` to `krakenAllSome` helper rename for Lean 4.35 compatibility. All other reused dependency sources must match the pinned commit. The [project manifest](manifest.json) records the theorem names, reuse information, and retained conditions.

Every Lean build runs through `tools/bounded-build`. The runner serializes builds under one lock and applies an 8 GiB memory limit, or 2 GiB with `--small`. It stops builds when system memory pressure reaches 24 GB.

### Binary artifact

The `binary/open-library/` directory contains an open relocatable assembly of 39 exported native texts. Its external references remain unresolved. The object is neither the original FFmpeg executable nor a closed linked image.

The object checks establish export identity, instruction boundaries, mnemonics, and address-size prefixes. They do not prove full operand equivalence. The [object validation report](binary/open-library/validation.json) records those checks and their scope.
