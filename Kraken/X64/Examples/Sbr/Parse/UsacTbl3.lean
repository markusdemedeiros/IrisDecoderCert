import Kraken.X64.Examples.Sbr.Parse.UsacBase

/-!
# `ff_aac_sbr_decode_usac_data`: the table and the variant at each label, part 3

One `rfl` lemma per label, so that a block proof rewrites only its own labels (unfolding the
109-way matches by `simp` is too slow).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]

theorem tbl_L3715 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3715" s = T_L3715 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3715 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3715" s = 1180591620717411303424 := rfl
theorem tbl_L3724 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3724" s = T_L3724 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3724 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3724" s = 1180591620717411303424 := rfl
theorem tbl_L3734 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3734" s = T_L3734 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3734 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3734" s = 1180591620717411303424 := rfl
theorem tbl_L3750 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3750" s = T_L3750 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3750 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3750" s = 1180591620717411303424 := rfl
theorem tbl_L3763 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3763" s = T_L3763 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3763 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3763" s = 1180591620717411303424 := rfl
theorem tbl_L377f (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L377f" s = T_L377f k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L377f (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L377f" s = 1180591620717411303424 := rfl
theorem tbl_L379a (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L379a" s = T_L379a k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L379a (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L379a" s = 1180591620717411303424 := rfl
theorem tbl_L37b3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L37b3" s = T_L37b3 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L37b3 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L37b3" s = 1180591620717411303424 := rfl
theorem tbl_L37cb (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L37cb" s = T_L37cb k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L37cb (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L37cb" s = 1180591620717411303424 := rfl
theorem tbl_L37e3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L37e3" s = T_L37e3 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L37e3 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L37e3" s = 1180591620717411303424 := rfl
theorem tbl_L37fe (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L37fe" s = T_L37fe k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L37fe (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L37fe" s = 1180591620717411303424 := rfl
theorem tbl_L3819 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3819" s = T_L3819 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3819 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3819" s = 1180591620717411303424 := rfl
theorem tbl_L382e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L382e" s = T_L382e k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L382e (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L382e" s = 1180591620717411303424 := rfl
theorem tbl_L3847 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3847" s = T_L3847 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3847 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3847" s = 1180591620717411303424 := rfl
theorem tbl_L3860 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3860" s = T_L3860 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3860 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3860" s = 1180591620717411303424 := rfl
theorem tbl_L3874 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3874" s = T_L3874 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3874 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3874" s = 1180591620717411303424 := rfl
theorem tbl_L387c (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L387c" s = T_L387c k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L387c (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L387c" s = 1180591620717411303424 := rfl
theorem tbl_L3890 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3890" s = T_L3890 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3890 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3890" s = 1180591620717411303424 := rfl
theorem tbl_L3898 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3898" s = T_L3898 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3898 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3898" s = 1180591620717411303424 := rfl

end Kraken.Examples.Sbr.Usac
