import Kraken.X64.Examples.Sbr.Parse.UsacBase

/-!
# `ff_aac_sbr_decode_usac_data`: the table and the variant at each label, part 4

One `rfl` lemma per label, so that a block proof rewrites only its own labels (unfolding the
109-way matches by `simp` is too slow).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]

theorem tbl_L38b6 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L38b6" s = T_L38b6 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L38b6 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L38b6" s = 1180591620717411303424 := rfl
theorem tbl_L38be (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L38be" s = T_L38be k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L38be (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L38be" s = 1180591620717411303424 := rfl
theorem tbl_L38d5 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L38d5" s = T_L38d5 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L38d5 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L38d5" s = 1180591620717411303424 := rfl
theorem tbl_L38dd (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L38dd" s = T_L38dd k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L38dd (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L38dd" s = 1180591620717411303424 := rfl
theorem tbl_L3913 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3913" s = T_L3913 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3913 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3913" s = 1180591620717411303424 := rfl
theorem tbl_L3933 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3933" s = T_L3933 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3933 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3933" s = 1180591620717411303424 := rfl
theorem tbl_L394e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L394e" s = T_L394e k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L394e (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L394e" s = 1180591620717411303424 := rfl
theorem tbl_L395d (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L395d" s = T_L395d k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L395d (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L395d" s = 1180591620717411303424 := rfl
theorem tbl_L3972 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3972" s = T_L3972 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3972 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3972" s = 1180591620717411303424 := rfl
theorem tbl_L3981 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3981" s = T_L3981 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3981 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3981" s = 1180591620717411303424 := rfl
theorem tbl_L3999 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3999" s = T_L3999 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3999 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3999" s = 1180591620717411303424 := rfl
theorem tbl_L39b8 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L39b8" s = T_L39b8 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L39b8 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L39b8" s = 1180591620717411303424 := rfl
theorem tbl_L39c6 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L39c6" s = T_L39c6 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L39c6 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L39c6" s = 1180591620717411303424 := rfl
theorem tbl_L39d8 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L39d8" s = T_L39d8 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L39d8 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L39d8" s = 1180591620717411303424 := rfl
theorem tbl_L39ec (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L39ec" s = T_L39ec k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L39ec (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L39ec" s = 1180591620717411303424 := rfl
theorem tbl_L39f4 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L39f4" s = T_L39f4 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L39f4 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L39f4" s = 1180591620717411303424 := rfl
theorem tbl_L3a0f (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a0f" s = T_L3a0f k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3a0f (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3a0f" s = 1180591620717411303424 := rfl
theorem tbl_L3a17 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a17" s = T_L3a17 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3a17 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3a17" s = 1180591620717411303424 := rfl
theorem tbl_L3a2b (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3a2b" s = T_L3a2b k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3a2b (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3a2b" s = 1180591620717411303424 := rfl

end Kraken.Examples.Sbr.Usac
