import Kraken.X64.Examples.Sbr.Parse.UsacBase

/-!
# `ff_aac_sbr_decode_usac_data`: the table and the variant at each label, part 1

One `rfl` lemma per label, so that a block proof rewrites only its own labels (unfolding the
109-way matches by `simp` is too slow).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]

theorem tbl_entry (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data" s = T_entry k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_entry (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data" s = 1180591620717411303424 := rfl
theorem tbl_L3361 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3361" s = T_L3361 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3361 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3361" s = 1180591620717411303424 := rfl
theorem tbl_L3388 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3388" s = T_L3388 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3388 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3388" s = 1180591620717411303424 := rfl
theorem tbl_L33a3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L33a3" s = T_L33a3 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L33a3 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L33a3" s = 1180591620717411303424 := rfl
theorem tbl_L33ba (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L33ba" s = T_L33ba k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L33ba (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L33ba" s = 1180591620717411303424 := rfl
theorem tbl_L33e6 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L33e6" s = T_L33e6 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L33e6 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L33e6" s = 1180591620717411303424 := rfl
theorem tbl_L3410 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3410" s = T_L3410 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3410 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3410" s = 1180591620717411303424 := rfl
theorem tbl_L343d (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L343d" s = T_L343d k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L343d (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L343d" s = 1180591620717411303424 := rfl
theorem tbl_L3475 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3475" s = T_L3475 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3475 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3475" s = 1180591620717411303424 := rfl
theorem tbl_L34b0 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L34b0" s = T_L34b0 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L34b0 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L34b0" s = 1180591620717411303424 := rfl
theorem tbl_L34dd (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L34dd" s = T_L34dd k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L34dd (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L34dd" s = 1180591620717411303424 := rfl
theorem tbl_L34f7 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L34f7" s = T_L34f7 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L34f7 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L34f7" s = 1180591620717411303424 := rfl
theorem tbl_L350f (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L350f" s = T_L350f k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L350f (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L350f" s = 1180591620717411303424 := rfl
theorem tbl_L3523 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3523" s = T_L3523 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3523 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3523" s = 1180591620717411303424 := rfl
theorem tbl_L353a (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L353a" s = T_L353a k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L353a (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L353a" s = 1180591620717411303424 := rfl
theorem tbl_L354e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L354e" s = T_L354e k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L354e (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L354e" s = 1180591620717411303424 := rfl
theorem tbl_L3569 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L3569" s = T_L3569 k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L3569 (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L3569" s = 1180591620717411303424 := rfl
theorem tbl_L358e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L358e" s = T_L358e k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L358e (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L358e" s = 1180591620717411303424 := rfl
theorem tbl_L359b (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) :
    table k A ra t₀ "ff_aac_sbr_decode_usac_data.L359b" s = T_L359b k A ra t₀ s := rfl
omit [CodeEnv] in
theorem var_L359b (s : MachineData) :
    var "ff_aac_sbr_decode_usac_data.L359b" s = 1180591620717411303424 := rfl

end Kraken.Examples.Sbr.Usac
