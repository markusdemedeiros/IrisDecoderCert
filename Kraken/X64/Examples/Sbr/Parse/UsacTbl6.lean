import Kraken.X64.Examples.Sbr.Parse.UsacBase

/-!
# `ff_aac_sbr_decode_usac_data`: the table and the variant at each label, part 6

One `rfl` lemma per label, so that a block proof rewrites only its own labels (unfolding the
109-way matches by `simp` is too slow).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]

theorem tbl_L3ce3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ce3" s = T_L3ce3 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3ce3 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3ce3" s =
      147573952589676412928 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat := rfl
theorem tbl_L3d23 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3d23" s = T_L3d23 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3d23 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3d23" s = 110680464442257309696 := rfl
theorem tbl_L3d2d (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3d2d" s = T_L3d2d k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3d2d (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3d2d" s = 73786976294838206464 := rfl
theorem tbl_L3d64 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3d64" s = T_L3d64 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3d64 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3d64" s = 332041393326771929088 := rfl
theorem tbl_L3d6e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3d6e" s = T_L3d6e k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3d6e (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3d6e" s =
      295147905179352825856 + (s.regs.get64 .rsi - s.regs.get64 .rax).toNat := rfl
theorem tbl_L3da4 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3da4" s = T_L3da4 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3da4 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3da4" s =
      295147905179352825856 + (s.regs.get64 .rsi - s.regs.get64 .rax).toNat := rfl
theorem tbl_L3de8 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3de8" s = T_L3de8 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3de8 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3de8" s = 258254417031933722624 := rfl
theorem tbl_L3e17 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3e17" s = T_L3e17 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3e17 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3e17" s = 221360928884514619392 := rfl
theorem tbl_L3e50 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3e50" s = T_L3e50 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3e50 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3e50" s = 184467440737095516160 := rfl
theorem tbl_L3e75 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3e75" s = T_L3e75 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3e75 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3e75" s =
      147573952589676412928 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat := rfl
theorem tbl_L3eac (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3eac" s = T_L3eac k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3eac (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3eac" s =
      147573952589676412928 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat := rfl
theorem tbl_L3ef1 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ef1" s = T_L3ef1 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3ef1 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3ef1" s = 36893488147419103232 := rfl
theorem tbl_done (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.done" s = T_done k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_done (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.done" s = 0 := rfl
theorem tbl_L3f00 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3f00" s = T_L3f00 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3f00 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3f00" s = 0 := rfl

end Kraken.Examples.Sbr.Usac
