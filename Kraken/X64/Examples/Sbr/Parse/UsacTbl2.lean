import Kraken.X64.Examples.Sbr.Parse.UsacBase

/-!
# `ff_aac_sbr_decode_usac_data`: the table and the variant at each label, part 2

One `rfl` lemma per label, so that a block proof rewrites only its own labels (unfolding the
109-way matches by `simp` is too slow).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]

theorem tbl_L35a3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L35a3" s = T_L35a3 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L35a3 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L35a3" s = 1180591620717411303424 := rfl
theorem tbl_L35a5 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L35a5" s = T_L35a5 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L35a5 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L35a5" s = 1180591620717411303424 := rfl
theorem tbl_L35b5 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L35b5" s = T_L35b5 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L35b5 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L35b5" s = 1180591620717411303424 := rfl
theorem tbl_L35bf (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L35bf" s = T_L35bf k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L35bf (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L35bf" s = 1180591620717411303424 := rfl
theorem tbl_L35d7 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L35d7" s = T_L35d7 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L35d7 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L35d7" s = 1180591620717411303424 := rfl
theorem tbl_L35ea (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L35ea" s = T_L35ea k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L35ea (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L35ea" s = 1180591620717411303424 := rfl
theorem tbl_L35f5 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L35f5" s = T_L35f5 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L35f5 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L35f5" s = 1180591620717411303424 := rfl
theorem tbl_L3609 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3609" s = T_L3609 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3609 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3609" s = 1180591620717411303424 := rfl
theorem tbl_L3621 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3621" s = T_L3621 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3621 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3621" s = 1180591620717411303424 := rfl
theorem tbl_L3630 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3630" s = T_L3630 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3630 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3630" s = 1180591620717411303424 := rfl
theorem tbl_L3644 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3644" s = T_L3644 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3644 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3644" s = 1180591620717411303424 := rfl
theorem tbl_L3652 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3652" s = T_L3652 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3652 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3652" s = 1180591620717411303424 := rfl
theorem tbl_L3666 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3666" s = T_L3666 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3666 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3666" s = 1180591620717411303424 := rfl
theorem tbl_L366e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L366e" s = T_L366e k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L366e (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L366e" s = 1180591620717411303424 := rfl
theorem tbl_L3682 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3682" s = T_L3682 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3682 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3682" s = 1180591620717411303424 := rfl
theorem tbl_L368a (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L368a" s = T_L368a k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L368a (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L368a" s = 1180591620717411303424 := rfl
theorem tbl_L36c0 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L36c0" s = T_L36c0 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L36c0 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L36c0" s = 73786976294838206464 := rfl
theorem tbl_L36c7 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L36c7" s = T_L36c7 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L36c7 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L36c7" s = 1180591620717411303424 := rfl
theorem tbl_L36fa (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L36fa" s = T_L36fa k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L36fa (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L36fa" s = 1180591620717411303424 := rfl

end Kraken.Examples.Sbr.Usac
