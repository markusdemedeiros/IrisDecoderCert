import Kraken.X64.Examples.Sbr.Parse.TlimBase

/-!
# `sbr_make_f_tablelim`: the variant at each label

`var` at a literal label, proved once by `rfl` (unfolding `var` with `simp` inside a block is
expensive: the match has one string pattern per label).
-/

open Kraken Kraken.SysV Mem

namespace Kraken.Examples.Sbr.Tlim

theorem var_entry (s : MachineData) : var "sbr_make_f_tablelim" s = 2 ^ 50 := rfl

theorem var_L3f22 (s : MachineData) : var "sbr_make_f_tablelim.L3f22" s = 2 ^ 50 := rfl

theorem var_L3f31 (s : MachineData) : var "sbr_make_f_tablelim.L3f31" s = 2 ^ 50 := rfl

theorem var_L3f3a (s : MachineData) : var "sbr_make_f_tablelim.L3f3a" s = 2 ^ 50 := rfl

theorem var_L3f59 (s : MachineData) : var "sbr_make_f_tablelim.L3f59" s = 2 ^ 50 := rfl

theorem var_L3f65 (s : MachineData) : var "sbr_make_f_tablelim.L3f65" s = 2 ^ 50 := rfl

theorem var_L3f77 (s : MachineData) : var "sbr_make_f_tablelim.L3f77" s = 2 ^ 50 := rfl

theorem var_L3f89 (s : MachineData) : var "sbr_make_f_tablelim.L3f89" s = 2 ^ 50 := rfl

theorem var_L3f9b (s : MachineData) : var "sbr_make_f_tablelim.L3f9b" s = 2 ^ 50 := rfl

theorem var_L3fad (s : MachineData) : var "sbr_make_f_tablelim.L3fad" s = 2 ^ 50 := rfl

theorem var_L3fbf (s : MachineData) : var "sbr_make_f_tablelim.L3fbf" s = 2 ^ 50 := rfl

theorem var_L3fcc (s : MachineData) : var "sbr_make_f_tablelim.L3fcc" s = 2 ^ 50 := rfl

theorem var_L3ff5 (s : MachineData) : var "sbr_make_f_tablelim.L3ff5" s = 2 ^ 50 := rfl

theorem var_L4000 (s : MachineData) : var "sbr_make_f_tablelim.L4000" s = 2 ^ 50 := rfl

theorem var_L400a (s : MachineData) : var "sbr_make_f_tablelim.L400a" s = 2 ^ 50 := rfl

theorem var_L4020 (s : MachineData) : var "sbr_make_f_tablelim.L4020" s = 2 ^ 50 := rfl

theorem var_L4026 (s : MachineData) : var "sbr_make_f_tablelim.L4026" s = 2 ^ 50 := rfl

theorem var_L403f (s : MachineData) : var "sbr_make_f_tablelim.L403f" s = 2 ^ 50 := rfl

theorem var_L4060 (s : MachineData) : var "sbr_make_f_tablelim.L4060" s = QV (stkPhi s (rN s .rcx)) 3500 := rfl

theorem var_L4068 (s : MachineData) : var "sbr_make_f_tablelim.L4068" s = QV (stkPhi s (rN s .rcx)) 3500 := rfl

theorem var_L4090 (s : MachineData) : var "sbr_make_f_tablelim.L4090" s = QV (phiC s) 3000 := rfl

theorem var_L40c3 (s : MachineData) : var "sbr_make_f_tablelim.L40c3" s = QV (phiC s) 3000 := rfl

theorem var_L40c9 (s : MachineData) : var "sbr_make_f_tablelim.L40c9" s = QV (phiC s) 3000 := rfl

theorem var_L40e0 (s : MachineData) : var "sbr_make_f_tablelim.L40e0" s = QV (phiC s) 3000 := rfl

theorem var_L40ec (s : MachineData) : var "sbr_make_f_tablelim.L40ec" s = QV (phiC s) 3000 := rfl

theorem var_L40f0 (s : MachineData) : var "sbr_make_f_tablelim.L40f0" s = QV (phiC s) 3000 := rfl

theorem var_L40f7 (s : MachineData) : var "sbr_make_f_tablelim.L40f7" s = QV (phiC s) 3000 := rfl

theorem var_L4105 (s : MachineData) : var "sbr_make_f_tablelim.L4105" s = QV (phiC s) 3000 := rfl

theorem var_L4110 (s : MachineData) : var "sbr_make_f_tablelim.L4110" s = QV (phiC s) 3000 := rfl

theorem var_L4120 (s : MachineData) : var "sbr_make_f_tablelim.L4120" s = QV (phiC s) 3000 := rfl

theorem var_L4130 (s : MachineData) : var "sbr_make_f_tablelim.L4130" s = QV (phiC s) 3000 := rfl

theorem var_L4150 (s : MachineData) : var "sbr_make_f_tablelim.L4150" s = QV (phiC s) (1000 + 4 * dP s) := rfl

theorem var_L4164 (s : MachineData) : var "sbr_make_f_tablelim.L4164" s = QV (phiC s) (if lle s then 1000 + 4 * dP s + 3 else 1000) := rfl

theorem var_L4169 (s : MachineData) : var "sbr_make_f_tablelim.L4169" s = QV (phiC s) (1000 + 4 * dP s + 3) := rfl

theorem var_L4170 (s : MachineData) : var "sbr_make_f_tablelim.L4170" s = QV (phiC s) (1000 + 4 * dP s + 3) := rfl

theorem var_L4190 (s : MachineData) : var "sbr_make_f_tablelim.L4190" s = QV (phiC s) (1000 + 4 * dP s + 1) := rfl

theorem var_L4194 (s : MachineData) : var "sbr_make_f_tablelim.L4194" s = QV (phiC s) (if lle s then 1000 + 4 * dP s + 2 else 1001) := rfl

theorem var_L4199 (s : MachineData) : var "sbr_make_f_tablelim.L4199" s = QV (phiC s) (1000 + 4 * dP s + 2) := rfl

theorem var_L41b0 (s : MachineData) : var "sbr_make_f_tablelim.L41b0" s = QV (phiC s) 900 := rfl

theorem var_L41b4 (s : MachineData) : var "sbr_make_f_tablelim.L41b4" s = QV (phiC s) 900 := rfl

theorem var_L41ca (s : MachineData) : var "sbr_make_f_tablelim.L41ca" s = QV (phiC s) 900 := rfl

theorem var_L41d3 (s : MachineData) : var "sbr_make_f_tablelim.L41d3" s = QV (phiC s) 900 := rfl

theorem var_L41e0 (s : MachineData) : var "sbr_make_f_tablelim.L41e0" s = QV (phiC s) (500 + (rN s .rdx - rN s .r8) / 2) := rfl

theorem var_L41f7 (s : MachineData) : var "sbr_make_f_tablelim.L41f7" s = QV (phiC s) 400 := rfl

theorem var_L4200 (s : MachineData) : var "sbr_make_f_tablelim.L4200" s = QV (phiC s) 300 := rfl

theorem var_L4211 (s : MachineData) : var "sbr_make_f_tablelim.L4211" s = QV (phiC s) 300 := rfl

theorem var_L421b (s : MachineData) : var "sbr_make_f_tablelim.L421b" s = QV (phiC s) 300 := rfl

theorem var_L4250 (s : MachineData) : var "sbr_make_f_tablelim.L4250" s = QV (phiC s) 300 := rfl

theorem var_L425a (s : MachineData) : var "sbr_make_f_tablelim.L425a" s = QV (phiC s) 300 := rfl

theorem var_L4280 (s : MachineData) : var "sbr_make_f_tablelim.L4280" s = QV (phiC s) 3000 := rfl

theorem var_L429d (s : MachineData) : var "sbr_make_f_tablelim.L429d" s = 2 ^ 20 := rfl

theorem var_L42b6 (s : MachineData) : var "sbr_make_f_tablelim.L42b6" s = 2 ^ 20 := rfl

theorem var_L42bc (s : MachineData) : var "sbr_make_f_tablelim.L42bc" s = 2 ^ 20 := rfl

theorem var_L42d0 (s : MachineData) : var "sbr_make_f_tablelim.L42d0" s = 64 * mu s := rfl

theorem var_L42eb (s : MachineData) : var "sbr_make_f_tablelim.L42eb" s = 64 * mu s + 63 := rfl

theorem var_L42fa (s : MachineData) : var "sbr_make_f_tablelim.L42fa" s = 64 * mu s + 62 := rfl

theorem var_L4312 (s : MachineData) : var "sbr_make_f_tablelim.L4312" s = 64 * mu s + 61 := rfl

theorem var_L4317 (s : MachineData) : var "sbr_make_f_tablelim.L4317" s = 64 * mu s + 60 := rfl

theorem var_L4323 (s : MachineData) : var "sbr_make_f_tablelim.L4323" s = 64 * mu s + 59 := rfl

theorem var_L4330 (s : MachineData) : var "sbr_make_f_tablelim.L4330" s = 64 * mu s + 40 + 2 * (rN s .r8 - rN s .r9) := rfl

theorem var_L4338 (s : MachineData) : var "sbr_make_f_tablelim.L4338" s = 64 * mu s + 39 + 2 * (rN s .r8 - rN s .r9) := rfl

theorem var_L4340 (s : MachineData) : var "sbr_make_f_tablelim.L4340" s = 64 * mu s + 38 := rfl

theorem var_L4342 (s : MachineData) : var "sbr_make_f_tablelim.L4342" s = 64 * mu s + 37 := rfl

theorem var_L4350 (s : MachineData) : var "sbr_make_f_tablelim.L4350" s = 64 * mu s + 20 + 2 * (rN s .r8 - rN s .rdx) := rfl

theorem var_L435b (s : MachineData) : var "sbr_make_f_tablelim.L435b" s = 64 * mu s + 19 + 2 * (rN s .r8 - rN s .rdx) := rfl

theorem var_L4363 (s : MachineData) : var "sbr_make_f_tablelim.L4363" s = 64 * mu s + 2 := rfl

theorem var_L4370 (s : MachineData) : var "sbr_make_f_tablelim.L4370" s = 64 * mu s + 1 := rfl

theorem var_L4385 (s : MachineData) : var "sbr_make_f_tablelim.L4385" s = 2 ^ 50 := rfl

theorem var_L438a (s : MachineData) : var "sbr_make_f_tablelim.L438a" s = 0 := rfl

theorem var_L4398 (s : MachineData) : var "sbr_make_f_tablelim.L4398" s = 0 := rfl

theorem var_L43a4 (s : MachineData) : var "sbr_make_f_tablelim.L43a4" s = 0 := rfl

theorem var_L43bd (s : MachineData) : var "sbr_make_f_tablelim.L43bd" s = 0 := rfl

theorem var_done (s : MachineData) : var "sbr_make_f_tablelim.done" s = 0 := rfl

theorem var_L43cd (s : MachineData) : var "sbr_make_f_tablelim.L43cd" s = 2 ^ 50 := rfl

theorem var_L43d2 (s : MachineData) : var "sbr_make_f_tablelim.L43d2" s = 2 ^ 50 := rfl

theorem var_L43d7 (s : MachineData) : var "sbr_make_f_tablelim.L43d7" s = 2 ^ 50 := rfl

theorem var_L43dc (s : MachineData) : var "sbr_make_f_tablelim.L43dc" s = 2 ^ 50 := rfl

theorem var_L43e1 (s : MachineData) : var "sbr_make_f_tablelim.L43e1" s = 2 ^ 50 := rfl

theorem var_L43e6 (s : MachineData) : var "sbr_make_f_tablelim.L43e6" s = 2 ^ 50 := rfl

theorem var_L43eb (s : MachineData) : var "sbr_make_f_tablelim.L43eb" s = 2 ^ 50 := rfl

theorem var_L43f0 (s : MachineData) : var "sbr_make_f_tablelim.L43f0" s = 2 ^ 50 := rfl

end Kraken.Examples.Sbr.Tlim
