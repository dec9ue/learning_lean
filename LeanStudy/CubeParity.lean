import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Simps.Basic

open Fin

/--
  equivalence between cube parity property related with TPPMark 2025
  base definitions are taken from https://github.com/auto-res/tpp2025/blob/main/tpp2025/Tpp2025.lean
-/


def PosNat := { n : Nat // n > 0 }

instance (n : Nat) : OfNat PosNat (n + 1) where
  ofNat := ⟨ n+1, Nat.succ_pos n ⟩

instance (n : PosNat) : NeZero n.val where
  out := Nat.ne_of_gt n.property

def Cube (n : PosNat) := Fin n.val → Fin n.val → Fin n.val → ZMod 2

namespace Cube

variable {n : PosNat}

structure XYZ (n : ℕ) where
  X : Fin n → Fin n → ZMod 2
  Y : Fin n → Fin n → ZMod 2
  Z : Fin n → Fin n → ZMod 2

def corner_parity (c : Cube n) (x0 y0 z0 x1 y1 z1: Fin n.val) : ZMod 2 :=
  c x0 y0 z0 + c x0 y0 z1 +
  c x0 y1 z0 + c x0 y1 z1 +
  c x1 y0 z0 + c x1 y0 z1 +
  c x1 y1 z0 + c x1 y1 z1

theorem origin_parity_even_iff_any_subcube_parity_even
    {c : Cube n} :
    (∀ x0 y0 z0 : Fin n.val,
      corner_parity c 0 0 0 x0 y0 z0 = 0) ↔
    (∀ x0 y0 z0 x1 y1 z1 : Fin n.val,
      corner_parity c x0 y0 z0 x1 y1 z1 = 0) := by
  constructor
  · intro h x0 y0 z0 x1 y1 z1
    have : corner_parity c x0 y0 z0 x1 y1 z1 =
        corner_parity c 0 0 0 x0 y0 z0 +
        corner_parity c 0 0 0 x0 y0 z1 +
        corner_parity c 0 0 0 x0 y1 z0 +
        corner_parity c 0 0 0 x0 y1 z1 +
        corner_parity c 0 0 0 x1 y0 z0 +
        corner_parity c 0 0 0 x1 y0 z1 +
        corner_parity c 0 0 0 x1 y1 z0 +
        corner_parity c 0 0 0 x1 y1 z1 := by
        grind [corner_parity]
    grind
  . grind

end Cube
