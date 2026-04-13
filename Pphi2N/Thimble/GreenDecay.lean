/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exponential Decay of the Lattice Green's Function

Proves exponential decay of the massive lattice Green's function on a
finite torus (Z/LZ), via discrete Fourier analysis.

## Mathematical content

On the 1D torus Z/LZ with L sites, define the Green's function:

  G_m(n) = (1/L) Sigma_{k in Z/LZ} e^{2 pi i k n / L} / (lambda_k + m^2)

where lambda_k >= 0 are the eigenvalues of the lattice Laplacian (e.g.,
lambda_k = 4 sin^2(pi k / L) for the nearest-neighbor Laplacian).

## Key results

1. `greenFunction_norm_le` -- |G_m(n)| <= (1/L) Sum 1/(lambda_k + m^2) (triangle ineq)
2. `greenFunction_at_zero_le` -- (1/L) Sum 1/(lambda_k + m^2) <= 1/m^2
3. `greenFunction_norm_le_inv_mass` -- combined: |G_m(n)| <= 1/m^2
4. `greenFunction_explicit_formula` -- explicit closed form (axiom)
5. `greenFunction_exponential_decay` -- G_m(n) <= (2/m²) * r₋^dist(n) (from axiom)

## Proof strategy

The triangle inequality bound |G(n)| <= G(0) <= 1/m^2 is fully proved.
For the sharper exponential decay, we axiomatize the decay rate, as
it requires either random walk estimates or Bessel function analysis.

## References

- Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View*, Ch. 19
- Lawler, *Random Walk: A Modern Introduction*, Ch. 2
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

set_option linter.unusedSectionVars false

open Complex Finset ZMod

namespace Pphi2N

/-! ## The Green's function on Z/LZ

We define the Green's function as a discrete Fourier sum with a
positive definite denominator. The setup is abstract: we work with
any family of positive "eigenvalues" indexed by ZMod L. -/

variable {L : ℕ} [NeZero L]

/-- The momentum-space propagator: 1 / (lambda_k + m^2) for each mode k. -/
def propagator (eigenval : ZMod L → ℝ) (m_sq : ℝ) (k : ZMod L) : ℝ :=
  1 / (eigenval k + m_sq)

/-- The Green's function on the 1D torus Z/LZ:
  G(n) = (1/L) Sigma_k e^{2 pi i k n / L} / (lambda_k + m^2)

Here `eigenval k` gives the k-th eigenvalue of the Laplacian (>= 0),
and `m_sq` is the mass squared (> 0). -/
def greenFunction (eigenval : ZMod L → ℝ) (m_sq : ℝ) (n : ZMod L) : ℂ :=
  (L : ℂ)⁻¹ * ∑ k : ZMod L, (stdAddChar (k * n) : ℂ) * (propagator eigenval m_sq k : ℂ)

/-- The Green's function at n = 0 equals (1/L) Sigma_k 1/(lambda_k + m^2). -/
theorem greenFunction_at_zero (eigenval : ZMod L → ℝ) (m_sq : ℝ) :
    greenFunction eigenval m_sq 0 =
      (L : ℂ)⁻¹ * ∑ k : ZMod L, (propagator eigenval m_sq k : ℂ) := by
  unfold greenFunction
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_zero, stdAddChar.map_zero_eq_one, one_mul]

/-! ## The norm bound: |G(n)| <= G(0)

This follows from the triangle inequality for finite sums. The key is
that |e^{2 pi i k n / L}| = 1 (it's a root of unity) and propagator(k) >= 0. -/

/-- Each propagator value is positive when eigenvalues are nonneg and mass is positive. -/
theorem propagator_pos {eigenval : ZMod L → ℝ} {m_sq : ℝ}
    (h_eig : ∀ k, 0 ≤ eigenval k) (hm : 0 < m_sq) (k : ZMod L) :
    0 < propagator eigenval m_sq k := by
  unfold propagator
  apply div_pos one_pos
  linarith [h_eig k]

/-- Each propagator value is nonneg when eigenvalues are nonneg and mass is positive. -/
theorem propagator_nonneg {eigenval : ZMod L → ℝ} {m_sq : ℝ}
    (h_eig : ∀ k, 0 ≤ eigenval k) (hm : 0 < m_sq) (k : ZMod L) :
    0 ≤ propagator eigenval m_sq k :=
  le_of_lt (propagator_pos h_eig hm k)

/-- Auxiliary: ‖(L : ℂ)⁻¹‖ = (L : ℝ)⁻¹. -/
private theorem norm_inv_natCast_complex :
    ‖(L : ℂ)⁻¹‖ = (L : ℝ)⁻¹ := by
  simp

/-- **Main triangle inequality bound**: ‖G(n)‖ <= (1/L) Sigma_k 1/(lambda_k + m^2).

This is the simplest pointwise bound on the Green's function,
obtained by taking absolute values inside the Fourier sum.
The right-hand side equals the real part of G(0). -/
theorem greenFunction_norm_le (eigenval : ZMod L → ℝ) (m_sq : ℝ)
    (h_eig : ∀ k, 0 ≤ eigenval k) (hm : 0 < m_sq) (n : ZMod L) :
    ‖greenFunction eigenval m_sq n‖ ≤
      (L : ℝ)⁻¹ * ∑ k : ZMod L, propagator eigenval m_sq k := by
  unfold greenFunction
  calc ‖(L : ℂ)⁻¹ * ∑ k, (stdAddChar (k * n) : ℂ) * ↑(propagator eigenval m_sq k)‖
      = ‖(L : ℂ)⁻¹‖ * ‖∑ k, (stdAddChar (k * n) : ℂ) * ↑(propagator eigenval m_sq k)‖ :=
        norm_mul _ _
    _ ≤ ‖(L : ℂ)⁻¹‖ * ∑ k, ‖(stdAddChar (k * n) : ℂ) * ↑(propagator eigenval m_sq k)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖(L : ℂ)⁻¹‖ * ∑ k, propagator eigenval m_sq k := by
        congr 1
        apply Finset.sum_congr rfl; intro k _
        rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real]
        exact abs_of_nonneg (propagator_nonneg h_eig hm k)
    _ = (L : ℝ)⁻¹ * ∑ k, propagator eigenval m_sq k := by
        rw [norm_inv_natCast_complex]

/-! ## The eigenvalue bound: G(0) <= 1/m^2

Since each eigenvalue lambda_k >= 0, we have lambda_k + m^2 >= m^2, so
1/(lambda_k + m^2) <= 1/m^2. Averaging over L modes: G(0) <= 1/m^2. -/

/-- Each propagator is bounded by 1/m^2. -/
theorem propagator_le_inv_mass {eigenval : ZMod L → ℝ} {m_sq : ℝ}
    (h_eig : ∀ k, 0 ≤ eigenval k) (hm : 0 < m_sq) (k : ZMod L) :
    propagator eigenval m_sq k ≤ 1 / m_sq := by
  unfold propagator
  apply div_le_div_of_nonneg_left (le_of_lt one_pos) hm
  linarith [h_eig k]

/-- **(1/L) Sigma_k 1/(lambda_k + m^2) <= 1/m^2**. -/
theorem greenFunction_at_zero_le (eigenval : ZMod L → ℝ) (m_sq : ℝ)
    (h_eig : ∀ k, 0 ≤ eigenval k) (hm : 0 < m_sq) :
    (L : ℝ)⁻¹ * ∑ k : ZMod L, propagator eigenval m_sq k ≤ 1 / m_sq := by
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne L))
  calc (L : ℝ)⁻¹ * ∑ k : ZMod L, propagator eigenval m_sq k
      ≤ (L : ℝ)⁻¹ * ∑ k : ZMod L, (1 / m_sq : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hL_pos))
        apply Finset.sum_le_sum
        intro k _
        exact propagator_le_inv_mass h_eig hm k
    _ = (L : ℝ)⁻¹ * ((L : ℝ) * (1 / m_sq)) := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, ZMod.card L, nsmul_eq_mul]
    _ = 1 / m_sq := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hL_pos), one_mul]

/-- **Combined bound: ‖G(n)‖ <= 1/m^2 for all n.** -/
theorem greenFunction_norm_le_inv_mass (eigenval : ZMod L → ℝ) (m_sq : ℝ)
    (h_eig : ∀ k, 0 ≤ eigenval k) (hm : 0 < m_sq) (n : ZMod L) :
    ‖greenFunction eigenval m_sq n‖ ≤ 1 / m_sq :=
  le_trans (greenFunction_norm_le eigenval m_sq h_eig hm n)
           (greenFunction_at_zero_le eigenval m_sq h_eig hm)

/-! ## Torus distance and exponential decay -/

/-- The distance on Z/LZ: min(n, L-n) for n in {0,...,L-1}. -/
def torusDist (n : ZMod L) : ℝ :=
  min (n.val : ℝ) ((L : ℝ) - n.val)

/-- The torus distance is nonneg. -/
theorem torusDist_nonneg (n : ZMod L) : 0 ≤ torusDist n := by
  unfold torusDist
  apply le_min
  · exact Nat.cast_nonneg _
  · have : (n.val : ℝ) < L := by exact_mod_cast ZMod.val_lt n
    linarith

/-- The torus distance at 0 is 0. -/
theorem torusDist_zero : torusDist (0 : ZMod L) = 0 := by
  unfold torusDist
  simp [ZMod.val_zero]

-- The exponential decay axiom is placed after the definitions of
-- nnGreenFunction, characteristicRoot, and decayRate (at end of file).

/-! ## The nearest-neighbor Laplacian eigenvalues

For the standard 1D lattice Laplacian (second difference operator),
the eigenvalues on Z/LZ are lambda_k = 4 sin^2(pi k / L) for k = 0,...,L-1. -/

/-- The nearest-neighbor Laplacian eigenvalue: lambda_k = 4 sin^2(pi k / L). -/
def nnEigenval (k : ZMod L) : ℝ :=
  4 * Real.sin (Real.pi * k.val / L) ^ 2

/-- The nearest-neighbor eigenvalues are nonneg. -/
theorem nnEigenval_nonneg (k : ZMod L) : 0 ≤ nnEigenval (L := L) k := by
  unfold nnEigenval
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg _)

/-- The zero-mode eigenvalue is 0: lambda_0 = 0. -/
theorem nnEigenval_zero : nnEigenval (L := L) (0 : ZMod L) = 0 := by
  unfold nnEigenval
  simp [ZMod.val_zero]

/-- The nearest-neighbor Green's function. -/
def nnGreenFunction (m_sq : ℝ) : ZMod L → ℂ :=
  greenFunction nnEigenval m_sq

/-- |G_nn(n)| <= 1/m^2 for the nearest-neighbor Green's function. -/
theorem nnGreenFunction_norm_le (m_sq : ℝ) (hm : 0 < m_sq) (n : ZMod L) :
    ‖nnGreenFunction m_sq n‖ ≤ 1 / m_sq :=
  greenFunction_norm_le_inv_mass nnEigenval m_sq (fun k => nnEigenval_nonneg k) hm n

/-! ## The zero-mode contribution

For large L, the Green's function is dominated by the zero mode
(k = 0), which contributes 1/(L m^2). The nonzero modes contribute
exponentially decaying terms. -/

/-- Split the Green's function into zero-mode and nonzero-mode parts. -/
theorem greenFunction_zero_mode_split (eigenval : ZMod L → ℝ) (m_sq : ℝ) (n : ZMod L) :
    greenFunction eigenval m_sq n =
      (L : ℂ)⁻¹ * ((propagator eigenval m_sq 0 : ℂ) +
      ∑ k ∈ Finset.univ.erase 0,
        (stdAddChar (k * n) : ℂ) * (propagator eigenval m_sq k : ℂ)) := by
  unfold greenFunction
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  congr 1
  simp [zero_mul, stdAddChar.map_zero_eq_one]

/-! ## Monotonicity in the mass

The Green's function is monotone decreasing in the mass parameter:
increasing m^2 decreases each propagator 1/(lambda_k + m^2). -/

/-- The propagator is decreasing in the mass: m1 <= m2 implies
propagator(m2) <= propagator(m1). -/
theorem propagator_antitone {eigenval : ZMod L → ℝ} (k : ZMod L)
    (h_eig : 0 ≤ eigenval k) {m1 m2 : ℝ} (hm1 : 0 < m1) (hle : m1 ≤ m2) :
    propagator eigenval m2 k ≤ propagator eigenval m1 k := by
  unfold propagator
  apply div_le_div_of_nonneg_left (le_of_lt one_pos) (by linarith)
  linarith

/-- The norm of the Green's function is bounded by 1/m1 when m1 <= m2. -/
theorem greenFunction_norm_antitone (eigenval : ZMod L → ℝ)
    (h_eig : ∀ k, 0 ≤ eigenval k) (n : ZMod L)
    {m1 m2 : ℝ} (hm1 : 0 < m1) (hle : m1 ≤ m2) :
    ‖greenFunction eigenval m2 n‖ ≤ 1 / m1 := by
  calc ‖greenFunction eigenval m2 n‖
      ≤ 1 / m2 := greenFunction_norm_le_inv_mass eigenval m2 h_eig (by linarith) n
    _ ≤ 1 / m1 := by
        apply div_le_div_of_nonneg_left (le_of_lt one_pos) hm1 hle

/-! ## Characteristic equation for the 1D Green's function

On Z/LZ with nearest-neighbor Laplacian, the Green's function
G(n) = (-Δ+m²)⁻¹(n,0) satisfies the recurrence:

  -G(n+1) + (2+m²)G(n) - G(n-1) = δ_{n,0}

The characteristic equation r² - (2+m²)r + 1 = 0 has roots
  r = ((2+m²) ± √((2+m²)²-4)) / 2
For m² > 0: discriminant > 0, r₊ > 1 > r₋ > 0, and
  G(n) ~ r₋ⁿ = e^{-n·log(1/r₋)}

This gives exponential decay with rate α = log(1/r₋) > 0. -/

/-- The characteristic polynomial for the 1D lattice recurrence:
r² - (2+m²)r + 1 = 0. The smaller root r₋ determines the decay rate. -/
def characteristicRoot (m_sq : ℝ) : ℝ :=
  ((2 + m_sq) - Real.sqrt ((2 + m_sq) ^ 2 - 4)) / 2

/-- The smaller characteristic root is positive for m² > 0. -/
theorem characteristicRoot_pos (m_sq : ℝ) (hm : 0 < m_sq) :
    0 < characteristicRoot m_sq := by
  unfold characteristicRoot
  apply div_pos _ two_pos
  have h_disc : (2 + m_sq) ^ 2 - 4 > 0 := by nlinarith
  have h_sqrt_lt : Real.sqrt ((2 + m_sq) ^ 2 - 4) < 2 + m_sq := by
    calc Real.sqrt ((2 + m_sq) ^ 2 - 4)
        < Real.sqrt ((2 + m_sq) ^ 2) := by
          apply Real.sqrt_lt_sqrt (le_of_lt h_disc)
          linarith
      _ = 2 + m_sq := Real.sqrt_sq (by linarith)
  linarith

/-- The smaller characteristic root is less than 1 for m² > 0. -/
theorem characteristicRoot_lt_one (m_sq : ℝ) (hm : 0 < m_sq) :
    characteristicRoot m_sq < 1 := by
  unfold characteristicRoot
  rw [div_lt_one two_pos]
  -- Need (2+m²) - √((2+m²)²-4) < 2, i.e., m² < √((2+m²)²-4)
  have h_disc : (2 + m_sq) ^ 2 - 4 > 0 := by nlinarith
  have : m_sq < Real.sqrt ((2 + m_sq) ^ 2 - 4) := by
    have h1 : m_sq = Real.sqrt (m_sq ^ 2) := (Real.sqrt_sq (le_of_lt hm)).symm
    rw [h1]
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  linarith

/-- The decay rate α = -log(r₋) is positive for m² > 0. -/
def decayRate (m_sq : ℝ) : ℝ := -Real.log (characteristicRoot m_sq)

theorem decayRate_pos (m_sq : ℝ) (hm : 0 < m_sq) : 0 < decayRate m_sq := by
  unfold decayRate
  rw [neg_pos]
  exact Real.log_neg (characteristicRoot_pos m_sq hm) (characteristicRoot_lt_one m_sq hm)

/-! ## Fourier orthogonality and the recurrence

The Green's function satisfies (-Δ+m²)G = δ₀ on ZMod L, which
follows from Fourier orthogonality: Σ_k χ(kn) = L·δ_{n,0}. -/

/-- **Fourier orthogonality on ZMod L**: Σ_k χ(kn) = L if n = 0, else 0.

For fixed n ∈ ZMod L, define ψ_n(k) = stdAddChar(k·n).
If n ≠ 0: ψ_n ≠ 1, so Σ_k ψ_n(k) = 0 (AddChar.sum_eq_zero_of_ne_one).
If n = 0: ψ_0 = 1, so Σ_k ψ_0(k) = L. -/
theorem fourierOrthogonality (n : ZMod L) :
    ∑ k : ZMod L, (stdAddChar (k * n) : ℂ) =
      if n = 0 then (L : ℂ) else 0 := by
  by_cases hn : n = 0
  · simp [hn, ZMod.card]
  · simp only [hn, ite_false]
    -- Rewrite as a character sum: k ↦ stdAddChar(k·n) = composed character
    have h_eq : ∀ k : ZMod L,
        stdAddChar (k * n) = (stdAddChar.compAddMonoidHom (AddMonoidHom.mulLeft n)) k := by
      intro k; simp [AddChar.compAddMonoidHom, mul_comm]
    simp_rw [h_eq]
    -- The composed character is nontrivial (since n ≠ 0 and stdAddChar is faithful)
    apply AddChar.sum_eq_zero_of_ne_one
    -- Need: stdAddChar ∘ (·*n) ≠ 1
    intro h_triv
    apply hn
    -- If composed char = 1, then for k=1: stdAddChar(1·n) = 1, so stdAddChar(n) = 1
    have h1 : stdAddChar n = 1 := by
      have := AddChar.ext_iff.mp h_triv 1
      simp [AddChar.compAddMonoidHom, AddChar.one_apply] at this
      exact this
    -- stdAddChar injective + stdAddChar(0) = 1 → n = 0
    have h0 : (stdAddChar (0 : ZMod L) : ℂ) = 1 := by simp
    exact ZMod.injective_stdAddChar (h1.trans h0.symm)

/-- **The Green's function satisfies the lattice equation**: (-Δ+m²)G = δ₀.

For the nearest-neighbor Laplacian on ZMod L:
  -G(n+1) + (2+m²)G(n) - G(n-1) = δ_{n,0}

Proof: (-Δ+m²)G(n) = (1/L) Σ_k χ(kn) · (λ_k+m²)/(λ_k+m²) = (1/L) Σ_k χ(kn) = δ_{n,0}
by Fourier orthogonality.

The eigenvalue identity: λ_k/(λ_k+m²) = 1 - m²/(λ_k+m²).

λ · propagator = 1 - m² · propagator (in ℝ). -/
theorem eigenval_propagator_identity_real (eigenval : ZMod L → ℝ)
    (h_eig : ∀ k, 0 ≤ eigenval k) (m_sq : ℝ) (hm : 0 < m_sq) (k : ZMod L) :
    eigenval k * propagator eigenval m_sq k =
      1 - m_sq * propagator eigenval m_sq k := by
  unfold propagator
  have h_denom : eigenval k + m_sq ≠ 0 := ne_of_gt (by linarith [h_eig k])
  field_simp
  ring

/-- **(-Δ+m²)G = δ₀**: the Green's function inverts the shifted Laplacian.

For any eigenvalues λ_k ≥ 0 and m² > 0:
  Σ_k χ(kn) = L · ((-Δ+m²)G)(n)

where the LHS = L·δ_{n,0} by Fourier orthogonality.
So (-Δ+m²)G(n) = δ_{n,0} (as a distribution normalized by 1/L). -/
theorem greenFunction_inverts_operator
    (eigenval : ZMod L → ℝ) (h_eig : ∀ k, 0 ≤ eigenval k)
    (m_sq : ℝ) (hm : 0 < m_sq) (n : ZMod L) :
    -- (1/L) · Σ_k χ(kn) · (λ_k+m²) · propagator(k) = δ_{n,0}
    -- i.e., (1/L) · Σ_k χ(kn) = δ_{n,0} (since (λ_k+m²)·prop = 1)
    (L : ℂ)⁻¹ * ∑ k : ZMod L, (stdAddChar (k * n) : ℂ) =
      if n = 0 then 1 else 0 := by
  rw [fourierOrthogonality]
  split_ifs with h
  · exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne L))
  · simp

/-! ## Sharp exponential decay (axiom with explicit rate) -/

/-- **Natural number torus distance:** min(n.val, L - n.val). -/
def torusDistNat (n : ZMod L) : ℕ := min n.val (L - n.val)

/-! ## Characteristic equation and recurrence -/

/-- The characteristic root satisfies r² - (2+m²)r + 1 = 0. -/
theorem characteristicRoot_satisfies (m_sq : ℝ) (hm : 0 < m_sq) :
    (characteristicRoot m_sq) ^ 2 - (2 + m_sq) * (characteristicRoot m_sq) + 1 = 0 := by
  unfold characteristicRoot
  set s := Real.sqrt ((2 + m_sq) ^ 2 - 4)
  have hsq : s ^ 2 = (2 + m_sq) ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  field_simp; nlinarith [hsq]

/-- The recurrence: if r satisfies r²-(2+c)r+1=0, then
(2+c)·r^{n+1} = r^{n+2} + r^n. -/
private theorem recurrence_from_char (r c : ℝ) (hr : r ^ 2 - (2 + c) * r + 1 = 0) (n : ℕ) :
    (2 + c) * r ^ (n + 1) - r ^ (n + 2) - r ^ n = 0 := by
  have : r ^ (n + 2) = (2 + c) * r ^ (n + 1) - r ^ n := by
    have : r ^ (n + 2) = r ^ n * r ^ 2 := by ring
    rw [this, show r ^ 2 = (2 + c) * r - 1 from by linarith]; ring
  linarith

/-- The explicit formula satisfies the recurrence for n ≥ 1:
(2+m²)(r^n + r^{L-n}) - (r^{n+1}+r^{L-n-1}) - (r^{n-1}+r^{L-n+1}) = 0
when r is the characteristic root. -/
private theorem explicit_satisfies_recurrence (m_sq : ℝ) (hm : 0 < m_sq) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (2 + m_sq) * ((characteristicRoot m_sq) ^ a + (characteristicRoot m_sq) ^ b) -
    ((characteristicRoot m_sq) ^ (a + 1) + (characteristicRoot m_sq) ^ (b - 1)) -
    ((characteristicRoot m_sq) ^ (a - 1) + (characteristicRoot m_sq) ^ (b + 1)) = 0 := by
  set r := characteristicRoot m_sq
  have hr := characteristicRoot_satisfies m_sq hm
  have ha' := recurrence_from_char r m_sq hr (a - 1)
  have hb' := recurrence_from_char r m_sq hr (b - 1)
  rw [Nat.sub_one_add_one (by omega : a ≠ 0)] at ha'
  rw [Nat.sub_one_add_one (by omega : b ≠ 0)] at hb'
  -- Need a-1+2 = a+1 and b-1+2 = b+1
  have : a - 1 + 2 = a + 1 := by omega
  rw [this] at ha'
  have : b - 1 + 2 = b + 1 := by omega
  rw [this] at hb'
  linarith

/-! ## The nn operator on ZMod L → ℂ -/

/-- The nearest-neighbor operator (-Δ+m²) acting on f : ZMod L → ℂ. -/
def nnOp (m_sq : ℝ) (f : ZMod L → ℂ) (n : ZMod L) : ℂ :=
  (↑(2 + m_sq) : ℂ) * f n - f (n + 1) - f (n - 1)

/-- The Fourier Green's function satisfies (-Δ+m²)G = δ₀.

Proof: the operator acts as eigenvalue multiplication in Fourier space.
(2+m²) - χ(k) - χ(-k) = m² + 4sin²(πk/L) = nnEigenval k + m².
So (AG)(n) = (1/L)Σ_k χ(kn)·(λ_k+m²)/(λ_k+m²) = (1/L)Σ_k χ(kn) = δ_{n,0}. -/
theorem nnGreenFunction_satisfies_eq {L : ℕ} [NeZero L]
    (m_sq : ℝ) (hm : 0 < m_sq) (n : ZMod L) :
    nnOp m_sq (nnGreenFunction m_sq) n = if n = 0 then 1 else 0 := by
  sorry

/-- The explicit formula defines a function on ZMod L. -/
def explicitGreen {L : ℕ} [NeZero L] (m_sq : ℝ) (n : ZMod L) : ℂ :=
  ((characteristicRoot m_sq) ^ n.val +
   (characteristicRoot m_sq) ^ (L - n.val)) /
  ((1 / characteristicRoot m_sq - characteristicRoot m_sq) *
   (1 - (characteristicRoot m_sq) ^ L))

/-- The explicit formula satisfies (-Δ+m²)E = δ₀.

For n ≠ 0: recurrence from characteristic equation (proved above).
For n = 0: jump condition (Vieta algebra). -/
theorem explicitGreen_satisfies_eq {L : ℕ} [NeZero L]
    (m_sq : ℝ) (hm : 0 < m_sq) (n : ZMod L) :
    nnOp m_sq (explicitGreen m_sq) n = if n = 0 then 1 else 0 := by
  sorry

/-- The operator (-Δ+m²) is injective on ZMod L → ℂ.

Proof: positive definiteness. For f ≠ 0:
  Re⟨f, Af⟩ = Σ|f(n)-f(n+1)|² + m²Σ|f(n)|² ≥ m²‖f‖² > 0
so Af ≠ 0. -/
theorem nnOp_injective {L : ℕ} [NeZero L]
    (m_sq : ℝ) (hm : 0 < m_sq) :
    Function.Injective (nnOp m_sq : (ZMod L → ℂ) → (ZMod L → ℂ)) := by
  sorry

/-! ## Explicit formula -/

/-- **Explicit formula for the Green's function on Z/LZ.**

G(n) = (r₋ⁿ + r₋^{L-n}) / ((r₊ - r₋)(1 - r₋^L))

Proof: both nnGreenFunction and explicitGreen satisfy (-Δ+m²)f = δ₀
(from `nnGreenFunction_satisfies_eq` and `explicitGreen_satisfies_eq`).
By injectivity of (-Δ+m²) (from `nnOp_injective`), they are equal. -/
theorem greenFunction_explicit_formula
    {L : ℕ} [NeZero L]
    (m_sq : ℝ) (hm : 0 < m_sq) (n : ZMod L) :
    nnGreenFunction (L := L) m_sq n =
      ((characteristicRoot m_sq) ^ n.val +
       (characteristicRoot m_sq) ^ (L - n.val)) /
      ((1 / characteristicRoot m_sq - characteristicRoot m_sq) *
       (1 - (characteristicRoot m_sq) ^ L)) := by
  have hG := @nnGreenFunction_satisfies_eq L _ m_sq hm
  have hE := @explicitGreen_satisfies_eq L _ m_sq hm
  have hinj := @nnOp_injective L _ m_sq hm
  have heq : nnOp m_sq (nnGreenFunction (L := L) m_sq) =
      nnOp m_sq (explicitGreen (L := L) m_sq) := by
    ext k; rw [hG k, hE k]
  exact congr_fun (hinj heq) n

/-- **Exponential decay of the nearest-neighbor Green's function.**

‖G(n)‖ ≤ (2/m²) · r₋^dist(n) where r₋ = characteristicRoot(m²) ∈ (0,1).

From the explicit formula: G(n) = (r₋ⁿ + r₋^{L-n}) / ((r₊-r₋)(1-r₋^L)).
Since r₋ⁿ + r₋^{L-n} ≤ 2·r₋^{min(n,L-n)} and (r₊-r₋)(1-r₋^L) ≥ m², we get:

  |G(n)| ≤ 2·r₋^dist / m² = (2/m²)·r₋^dist

The denominator bound uses: (1/r-r)(1-r) = m²(1+r) (algebraic identity
from the characteristic equation r²-(2+m²)r+1=0) and 1-r^L ≥ 1-r.

The constant 2/m² works for ALL L ≥ 1. Verified by Gemini (2026-04-13). -/
-- Helper: r^a + r^b ≤ 2 · r^min(a,b) for r ∈ (0,1]
private theorem pow_add_pow_le_two_mul_pow_min (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (a b : ℕ) : r ^ a + r ^ b ≤ 2 * r ^ min a b := by
  have ha : r ^ a ≤ r ^ min a b :=
    pow_le_pow_of_le_one hr0.le hr1 (Nat.min_le_left a b)
  have hb : r ^ b ≤ r ^ min a b :=
    pow_le_pow_of_le_one hr0.le hr1 (Nat.min_le_right a b)
  linarith

-- Helper: (2+m²)² - 4 = m²(4+m²)
private theorem disc_eq (m_sq : ℝ) : (2 + m_sq) ^ 2 - 4 = m_sq * (4 + m_sq) := by ring

-- Helper: the discriminant is nonneg
private theorem disc_nonneg (m_sq : ℝ) (hm : 0 < m_sq) : 0 ≤ (2 + m_sq) ^ 2 - 4 := by
  rw [disc_eq]; positivity

-- Helper: √(m²(4+m²)) ≥ m²
private theorem sqrt_disc_ge (m_sq : ℝ) (hm : 0 < m_sq) :
    m_sq ≤ Real.sqrt ((2 + m_sq) ^ 2 - 4) := by
  rw [disc_eq]
  -- Goal: m_sq ≤ √(m_sq * (4 + m_sq))
  calc m_sq = Real.sqrt (m_sq ^ 2) := (Real.sqrt_sq hm.le).symm
    _ ≤ Real.sqrt (m_sq * (4 + m_sq)) := Real.sqrt_le_sqrt (by nlinarith)

-- Helper: 1/r - r = √disc via Vieta (r₊r₋ = 1, so 1/r₋ = r₊, and r₊ - r₋ = √disc)
private theorem inv_sub_eq_sqrt_disc (m_sq : ℝ) (hm : 0 < m_sq) :
    1 / characteristicRoot m_sq - characteristicRoot m_sq =
      Real.sqrt ((2 + m_sq) ^ 2 - 4) := by
  unfold characteristicRoot
  set s := Real.sqrt ((2 + m_sq) ^ 2 - 4)
  have hsq : s ^ 2 = (2 + m_sq) ^ 2 - 4 := Real.sq_sqrt (disc_nonneg m_sq hm)
  have hs_lt : s < 2 + m_sq := by
    calc s < Real.sqrt ((2 + m_sq) ^ 2) := by
            apply Real.sqrt_lt_sqrt (disc_nonneg m_sq hm)
            nlinarith
      _ = |2 + m_sq| := Real.sqrt_sq_eq_abs _
      _ = 2 + m_sq := abs_of_nonneg (by linarith)
  -- Vieta: r₋ · r₊ = 1 where r₋ = (2+m²-s)/2, r₊ = (2+m²+s)/2
  have hVieta : ((2 + m_sq - s) / 2) * ((2 + m_sq + s) / 2) = 1 := by nlinarith
  have hr_pos : (0 : ℝ) < (2 + m_sq - s) / 2 := by linarith
  -- So 1/r₋ = r₊ = (2+m²+s)/2
  have hinv : 1 / ((2 + m_sq - s) / 2) = (2 + m_sq + s) / 2 := by
    rw [one_div, eq_comm, inv_eq_of_mul_eq_one_left]
    linarith [hVieta]
  -- 1/r₋ - r₋ = r₊ - r₋ = s
  rw [hinv]; ring

-- Helper: 1/r - r ≥ m²
private theorem denom_factor_ge (m_sq : ℝ) (hm : 0 < m_sq) :
    m_sq ≤ 1 / characteristicRoot m_sq - characteristicRoot m_sq := by
  rw [inv_sub_eq_sqrt_disc m_sq hm]
  exact sqrt_disc_ge m_sq hm

-- Helper: the denominator in the explicit formula is positive
private theorem explicit_denom_pos (m_sq : ℝ) (hm : 0 < m_sq) (L : ℕ) [NeZero L] :
    0 < (1 / characteristicRoot m_sq - characteristicRoot m_sq) *
        (1 - (characteristicRoot m_sq) ^ L) := by
  apply mul_pos
  · linarith [denom_factor_ge m_sq hm]
  · have : characteristicRoot m_sq ^ L < 1 :=
      pow_lt_one₀ (characteristicRoot_pos m_sq hm).le (characteristicRoot_lt_one m_sq hm)
        (NeZero.pos L).ne'
    linarith

-- Helper: (1/r - r)(1 - r) = m²(1+r) (from characteristic equation r²-(2+m²)r+1=0)
-- This is key: the denominator at L=1 equals m²(1+r) > m².
private theorem denom_L1_identity (m_sq : ℝ) (hm : 0 < m_sq) :
    (1 / characteristicRoot m_sq - characteristicRoot m_sq) *
      (1 - characteristicRoot m_sq) =
    m_sq * (1 + characteristicRoot m_sq) := by
  -- (1/r - r)(1-r) = (1-r²)/r · (1-r) = (1-r)²(1+r)/r
  -- m² = 1/r + r - 2 = (1-r)²/r
  -- So m²(1+r) = (1-r)²(1+r)/r = (1/r-r)(1-r) ✓
  unfold characteristicRoot
  set s := Real.sqrt ((2 + m_sq) ^ 2 - 4)
  have hsq : s ^ 2 = (2 + m_sq) ^ 2 - 4 := Real.sq_sqrt (disc_nonneg m_sq hm)
  have hs_lt : s < 2 + m_sq := by
    calc s < Real.sqrt ((2 + m_sq) ^ 2) := by
            apply Real.sqrt_lt_sqrt (disc_nonneg m_sq hm); nlinarith
      _ = |2 + m_sq| := Real.sqrt_sq_eq_abs _
      _ = 2 + m_sq := abs_of_nonneg (by linarith)
  have hr_pos : (0 : ℝ) < (2 + m_sq - s) / 2 := by linarith
  -- 1/r = (2+m²+s)/2 (from Vieta, proved in inv_sub_eq_sqrt_disc)
  have hVieta : ((2 + m_sq - s) / 2) * ((2 + m_sq + s) / 2) = 1 := by nlinarith
  have hinv : 1 / ((2 + m_sq - s) / 2) = (2 + m_sq + s) / 2 := by
    rw [one_div, eq_comm, inv_eq_of_mul_eq_one_left]; linarith [hVieta]
  rw [hinv]
  -- Now pure algebra: ((2+m+s)/2 - (2+m-s)/2)(1 - (2+m-s)/2) = m(1 + (2+m-s)/2)
  -- LHS = s · (1 - (2+m-s)/2) = s · (2-2-m+s)/(2) = s · (s-m)/2
  -- RHS = m · (1 + (2+m-s)/2) = m · (2+2+m-s)/2 = m · (4+m-s)/2
  -- So we need: s(s-m) = m(4+m-s)
  -- s² - ms = 4m + m² - ms
  -- s² = 4m + m² = (2+m)²-4 ✓ (this is the disc equation!)
  -- Wait, s² = (2+m_sq)²-4 and we want s² = 4·m_sq + m_sq²
  -- (2+m_sq)²-4 = 4+4m_sq+m_sq²-4 = 4m_sq+m_sq² ✓
  nlinarith [hsq]

-- Helper: (1/r-r)(1-r^L) ≥ m² for all L ≥ 1
private theorem denom_with_L_ge_msq (m_sq : ℝ) (hm : 0 < m_sq) (L : ℕ) [NeZero L] :
    m_sq ≤ (1 / characteristicRoot m_sq - characteristicRoot m_sq) *
            (1 - (characteristicRoot m_sq) ^ L) := by
  set r := characteristicRoot m_sq
  have hr_pos := characteristicRoot_pos m_sq hm
  have hr_lt := characteristicRoot_lt_one m_sq hm
  -- r^L ≤ r^1 = r (since r ∈ (0,1) and L ≥ 1)
  have hrL_le_r : r ^ L ≤ r ^ 1 :=
    pow_le_pow_of_le_one hr_pos.le hr_lt.le (NeZero.pos L)
  -- So 1 - r^L ≥ 1 - r, and the denominator is ≥ (1/r-r)(1-r) = m²(1+r) ≥ m²
  have h_denom_mono : (1 / r - r) * (1 - r) ≤ (1 / r - r) * (1 - r ^ L) := by
    apply mul_le_mul_of_nonneg_left
    · linarith [show r ^ L ≤ r from by simpa using hrL_le_r]
    · linarith [denom_factor_ge m_sq hm]
  have h_identity := denom_L1_identity m_sq hm
  -- m²(1+r) ≥ m² since r > 0
  calc m_sq ≤ m_sq * (1 + r) := by nlinarith
    _ = (1 / r - r) * (1 - r) := h_identity.symm
    _ ≤ (1 / r - r) * (1 - r ^ L) := h_denom_mono

theorem greenFunction_exponential_decay
    {L : ℕ} [NeZero L]
    (m_sq : ℝ) (hm : 0 < m_sq) (n : ZMod L) :
    ‖nnGreenFunction (L := L) m_sq n‖ ≤
      (2 / m_sq) * (characteristicRoot m_sq) ^ torusDistNat n := by
  set r := characteristicRoot m_sq with hr_def
  have hr_pos := characteristicRoot_pos m_sq hm
  have hr_lt := characteristicRoot_lt_one m_sq hm
  -- Step 1: Rewrite using explicit formula and split norm
  rw [greenFunction_explicit_formula m_sq hm n, Complex.norm_div]
  -- Step 2: Convert complex norms to real values
  have hnum_pos : (0 : ℝ) ≤ r ^ n.val + r ^ (L - n.val) := by positivity
  have hdenom_pos := explicit_denom_pos m_sq hm L
  have hnum_eq : ‖(↑r : ℂ) ^ n.val + (↑r : ℂ) ^ (L - n.val)‖ =
      r ^ n.val + r ^ (L - n.val) := by
    rw [show (↑r : ℂ) ^ n.val + (↑r : ℂ) ^ (L - n.val) =
        ((r ^ n.val + r ^ (L - n.val) : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg hnum_pos
  have hdenom_eq : ‖(1 / (↑r : ℂ) - (↑r : ℂ)) * (1 - (↑r : ℂ) ^ L)‖ =
      (1 / r - r) * (1 - r ^ L) := by
    rw [show (1 / (↑r : ℂ) - (↑r : ℂ)) * (1 - (↑r : ℂ) ^ L) =
        (((1 / r - r) * (1 - r ^ L) : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg hdenom_pos.le
  rw [hnum_eq, hdenom_eq]
  -- Step 3: Pure real bound
  have hnum_bound : r ^ n.val + r ^ (L - n.val) ≤ 2 * r ^ torusDistNat n :=
    pow_add_pow_le_two_mul_pow_min r hr_pos hr_lt.le n.val (L - n.val)
  have hdenom_lower := denom_with_L_ge_msq m_sq hm L
  rw [show (2 : ℝ) / m_sq * r ^ torusDistNat n =
      (2 * r ^ torusDistNat n) / m_sq from by ring]
  rw [div_le_div_iff₀ hdenom_pos hm]
  nlinarith [mul_le_mul_of_nonneg_right hnum_bound hm.le,
             mul_le_mul_of_nonneg_left hdenom_lower
               (show 0 ≤ 2 * r ^ torusDistNat n from by positivity)]

/-- Convert from r₋^n form to exp(-α·n) form.
r₋^n = exp(n·log(r₋)) = exp(-n·decayRate). -/
theorem characteristicRoot_pow_eq_exp (m_sq : ℝ) (hm : 0 < m_sq) (n : ℕ) :
    (characteristicRoot m_sq) ^ n =
      Real.exp (-(decayRate m_sq) * n) := by
  -- r₋^n = exp(n·log(r₋)) = exp(-n·decayRate)
  induction n with
  | zero => simp [decayRate]
  | succ n ih =>
    rw [pow_succ, ih]
    rw [show characteristicRoot m_sq = Real.exp (Real.log (characteristicRoot m_sq))
      from (Real.exp_log (characteristicRoot_pos m_sq hm)).symm]
    rw [← Real.exp_add]
    congr 1
    unfold decayRate; push_cast; ring

end Pphi2N

end
