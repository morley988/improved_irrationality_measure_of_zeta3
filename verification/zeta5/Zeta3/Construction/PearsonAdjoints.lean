import Zeta3.Construction.PearsonRoots

/-!
# Algebraic adjoints implied by a Pearson identity

All hypotheses about the functional are displayed.  In particular, this
module does not assert the Pearson relation for the cubic integral.  It
proves the algebraic bridge from that relation to the adjoints needed by
the least-kernel-polynomial argument.
-/

noncomputable section
namespace Zeta3.Construction.Pearson
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem forward_adjoint (L : K[X] →ₗ[K] K) (A B : K[X])
    (hPearson : ∀ f : K[X], L (B * f.comp (X + 1)) = L (A * f))
    (f g : K[X]) :
    L (B * f.comp (X + 1) * g) = L (f * (A * g.comp (X - 1))) := by
  have h := hPearson (f * g.comp (X - 1))
  have hid : (g.comp (X - 1)).comp (X + 1) = g := by
    rw [comp_assoc]
    simp
  simp only [mul_comp, hid] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem backward_adjoint (L : K[X] →ₗ[K] K) (A B : K[X])
    (hPearson : ∀ f : K[X], L (B * f.comp (X + 1)) = L (A * f))
    (f g : K[X]) :
    L (A * f.comp (X - 1) * g) = L (f * (B * g.comp (X + 1))) := by
  have h := forward_adjoint L A B hPearson g f
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h.symm

theorem operatorD_self_adjoint (L : K[X] →ₗ[K] K) (A B : K[X])
    (hB : B.comp (-X) = -A)
    (hPearson : ∀ f : K[X], L (B * f.comp (X + 1)) = L (A * f))
    (f g : K[X]) : L (operatorD B f * g) = L (f * operatorD B g) := by
  have heq : operatorD B f * g =
      B * f.comp (X + 1) * g + A * f.comp (X - 1) * g -
        f * ((B + A) * g) := by
    rw [operatorD, hB]
    ring
  rw [heq, map_sub, map_add, forward_adjoint L A B hPearson,
    backward_adjoint L A B hPearson, ← map_add, ← map_sub]
  congr 1
  rw [operatorD, hB]
  ring

theorem evenPart_observation (L : K[X] →ₗ[K] K)
    (hEvenL : ∀ f : K[X], L (f.comp (-X)) = L f) (f : K[X]) :
    L (evenPart f) = L f := by
  rw [evenPart, ← Polynomial.smul_eq_C_mul, map_smul, map_add, hEvenL]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem evenPart_mul_even (f g : K[X]) (hg : g.comp (-X) = g) :
    evenPart f * g = evenPart (f * g) := by
  simp only [evenPart, mul_comp, hg]
  ring

theorem evenPart_pairing (L : K[X] →ₗ[K] K)
    (hEvenL : ∀ f : K[X], L (f.comp (-X)) = L f)
    (f g : K[X]) (hg : g.comp (-X) = g) :
    L (evenPart f * g) = L (f * g) := by
  rw [evenPart_mul_even f g hg, evenPart_observation L hEvenL]

def operatorQstar (A g : K[X]) : K[X] := evenPart (A * g.comp (X - 1))

def operatorRstar (B g : K[X]) : K[X] := operatorD B (X * g)

theorem operatorQ_adjoint (L : K[X] →ₗ[K] K) (A B : K[X])
    (hPearson : ∀ f : K[X], L (B * f.comp (X + 1)) = L (A * f))
    (hEvenL : ∀ f : K[X], L (f.comp (-X)) = L f)
    (f g : K[X]) (hf : f.comp (-X) = f) (hg : g.comp (-X) = g) :
    L (operatorQ B f * g) = L (f * operatorQstar A g) := by
  rw [operatorQ, evenPart_pairing L hEvenL _ _ hg,
    forward_adjoint L A B hPearson]
  have h := evenPart_pairing L hEvenL (A * g.comp (X - 1)) f hf
  simpa only [operatorQstar, mul_comm] using h.symm

theorem operatorR_adjoint (L : K[X] →ₗ[K] K) (A B : K[X])
    (hB : B.comp (-X) = -A)
    (hPearson : ∀ f : K[X], L (B * f.comp (X + 1)) = L (A * f))
    (f g : K[X]) :
    L (operatorR B f * g) = L (f * operatorRstar B g) := by
  rw [operatorR, show X * operatorD B f * g = operatorD B f * (X * g) by ring,
    operatorD_self_adjoint L A B hB hPearson]
  rfl

end Zeta3.Construction.Pearson
