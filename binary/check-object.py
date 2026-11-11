#!/usr/bin/env python3
"""Check object provenance, instruction boundaries, mnemonics and address sizes.

LLVM independently decodes every GNU-as instruction. This is deliberately a
limited encoding check, not a verified decoder or an operand-equivalence proof.
Full placement, data, relocation and callback obligations remain open.
"""
import ctypes
import hashlib
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
os.environ.setdefault("SBR_OBJ_DIR", "/nonexistent")
sys.path.insert(0, str(ROOT.parent / "scripts/sbr/tv"))
from tv import Elf


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check():
    directory = ROOT / "open-library"
    manifest = json.loads((directory / "manifest.json").read_text())
    assert manifest["object_sha256"] == sha(directory / "sbr.o")
    assert manifest["assembly_sha256"] == sha(directory / "sbr.S")
    elf = Elf(str(directory / "sbr.o"))
    sections = {s["name"]: s for s in elf.secs}
    libpath = os.environ.get("SBR_LLVM_LIBRARY", "/usr/lib/aarch64-linux-gnu/libLLVM.so.21.1")
    llvm = ctypes.CDLL(libpath)
    for name in ("LLVMInitializeX86TargetInfo", "LLVMInitializeX86TargetMC",
                 "LLVMInitializeX86Disassembler"):
        getattr(llvm, name)()
    llvm.LLVMCreateDisasm.argtypes = [ctypes.c_char_p, ctypes.c_void_p, ctypes.c_int,
                                     ctypes.c_void_p, ctypes.c_void_p]
    llvm.LLVMCreateDisasm.restype = ctypes.c_void_p
    decoder = llvm.LLVMCreateDisasm(b"x86_64-pc-linux-gnu", None, 0, None, None)
    assert decoder
    llvm.LLVMSetDisasmOptions.argtypes = [ctypes.c_void_p, ctypes.c_uint64]
    assert llvm.LLVMSetDisasmOptions(decoder, 4)  # Intel syntax.
    llvm.LLVMDisasmInstruction.argtypes = [ctypes.c_void_p, ctypes.c_void_p,
        ctypes.c_uint64, ctypes.c_uint64, ctypes.c_char_p, ctypes.c_size_t]
    llvm.LLVMDisasmInstruction.restype = ctypes.c_size_t
    llvm.LLVMDisasmDispose.argtypes = [ctypes.c_void_p]
    aliases = {(".nops", "nop"), ("mov", "movabs")}
    prefixes = {0xf0, 0xf2, 0xf3, 0x2e, 0x36, 0x3e, 0x26, 0x64, 0x65, 0x66, 0x67}
    count = 0
    for program in manifest["programs"]:
        filename = program["name"] + ".txt"
        source = ROOT / "texts" / filename
        regenerated = ROOT / "reexport" / filename
        assert sha(source) == program["source_sha256"], filename
        assert source.read_bytes() == regenerated.read_bytes(), f"Stale export: {filename}"
        section = sections[program["section"]]
        for cell in program["cells"]:
            if "instruction" not in cell:
                continue
            pos = section["off"] + cell["offset"]
            raw = elf.data[pos:pos + cell["size"]]
            assert raw.hex() == cell["encoding_before_relocation"]
            data = ctypes.create_string_buffer(raw)
            output = ctypes.create_string_buffer(512)
            size = llvm.LLVMDisasmInstruction(decoder, data, len(raw), cell["offset"], output, 512)
            decoded = output.value.decode().strip()
            assert size == len(raw), (filename, cell, size, decoded)
            expected_mnemonic = cell["instruction"].split()[0]
            actual_mnemonic = decoded.split()[0]
            assert expected_mnemonic == actual_mnemonic or \
                (expected_mnemonic, actual_mnemonic) in aliases, (filename, cell, decoded)
            if expected_mnemonic != ".nops":
                seen = set()
                for byte in raw:
                    if byte in prefixes or 0x40 <= byte <= 0x4f:
                        seen.add(byte)
                    else:
                        break
                aw = "w32" if 0x67 in seen else "w64"
                assert cell["widths"].split()[0] == "aw=" + aw, (filename, cell, decoded)
            count += 1
    llvm.LLVMDisasmDispose(decoder)
    assert count == manifest["instruction_count"]
    report = {"status": "passed", "programs": len(manifest["programs"]),
              "instructions": count, "object_sha256": manifest["object_sha256"],
              "fresh_lean_exports_match": True, "independent_decoder": libpath,
              "checks": ["object and source hashes", "fresh Lean text export equality",
                         "every instruction boundary", "mnemonics (explicit aliases)",
                         "address-size prefixes except padding"],
              "not_proved": ["full operand equivalence", "original FFmpeg binary identity",
                             "closed image placement", "external contracts"]}
    (directory / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    check()
