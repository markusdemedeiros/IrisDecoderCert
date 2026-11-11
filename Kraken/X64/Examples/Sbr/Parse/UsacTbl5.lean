import Kraken.X64.Examples.Sbr.Parse.UsacBase

/-!
# `ff_aac_sbr_decode_usac_data`: the table and the variant at each label, part 5

One `rfl` lemma per label, so that a block proof rewrites only its own labels (unfolding the
109-way matches by `simp` is too slow).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]

theorem tbl_L3a33 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a33" s = T_L3a33 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3a33 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3a33" s = 1180591620717411303424 := rfl
theorem tbl_L3a4e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a4e" s = T_L3a4e k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3a4e (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3a4e" s = 1180591620717411303424 := rfl
theorem tbl_L3a56 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a56" s = T_L3a56 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3a56 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3a56" s = 1180591620717411303424 := rfl
theorem tbl_L3a8c (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a8c" s = T_L3a8c k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3a8c (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3a8c" s = 1180591620717411303424 := rfl
theorem tbl_L3aac (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3aac" s = T_L3aac k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3aac (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3aac" s = 1180591620717411303424 := rfl
theorem tbl_L3ab1 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ab1" s = T_L3ab1 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3ab1 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3ab1" s = 184467440737095516160 := rfl
theorem tbl_L3ad4 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ad4" s = T_L3ad4 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3ad4 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3ad4" s = 147573952589676412928 := rfl
theorem tbl_L3ae0 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ae0" s = T_L3ae0 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3ae0 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3ae0" s =
      110680464442257309696 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat := rfl
theorem tbl_L3b17 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3b17" s = T_L3b17 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3b17 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3b17" s =
      110680464442257309696 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat := rfl
theorem tbl_L3b61 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3b61" s = T_L3b61 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3b61 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3b61" s = 73786976294838206464 := rfl
theorem tbl_L3b98 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3b98" s = T_L3b98 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3b98 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3b98" s = 368934881474191032320 := rfl
theorem tbl_L3ba2 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ba2" s = T_L3ba2 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3ba2 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3ba2" s =
      332041393326771929088 + (s.regs.get64 .rsi - s.regs.get64 .rax).toNat := rfl
theorem tbl_L3bd8 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3bd8" s = T_L3bd8 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3bd8 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3bd8" s =
      332041393326771929088 + (s.regs.get64 .rsi - s.regs.get64 .rax).toNat := rfl
theorem tbl_L3c1c (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3c1c" s = T_L3c1c k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3c1c (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3c1c" s = 295147905179352825856 := rfl
theorem tbl_L3c4b (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3c4b" s = T_L3c4b k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3c4b (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3c4b" s = 258254417031933722624 := rfl
theorem tbl_L3c84 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3c84" s = T_L3c84 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3c84 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3c84" s = 221360928884514619392 := rfl
theorem tbl_L3c9b (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3c9b" s = T_L3c9b k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3c9b (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3c9b" s = 110680464442257309696 := rfl
theorem tbl_L3ca2 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ca2" s = T_L3ca2 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3ca2 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3ca2" s = 184467440737095516160 := rfl
theorem tbl_L3cac (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3cac" s = T_L3cac k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3cac (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3cac" s =
      147573952589676412928 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat := rfl

end Kraken.Examples.Sbr.Usac
