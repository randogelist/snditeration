import Zetahyperbolic.Section2.RationalDomain
import Zetahyperbolic.Section2.TauGenerators
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Representation-independent moment functionals on actual rational functions

The domains are subspaces of `RatFunc ℚ`, not proof-carrying symbolic wrappers.
Their elements are precisely polynomial-plus-finite-simple-pole expressions.
Distinct nodes give unique coordinates, so every assignment of generator
values extends to a well-defined rational-function linear functional.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.SimplePole

variable {ι : Type*} [DecidableEq ι]

abbrev Domain (node : ι → ℚ) := LinearMap.range (realize node)

def coordinates (node : ι → ℚ) (hn : Function.Injective node) :
    Data ι ≃ₗ[ℚ] Domain node :=
  LinearEquiv.ofInjective (realize node) (realize_injective node hn)

def ofData (node : ι → ℚ) (d : Data ι) : Domain node :=
  (realize node).rangeRestrict d

@[simp] theorem ofData_coe (node : ι → ℚ) (d : Data ι) :
    (ofData node d : RatFunc ℚ) = realize node d := rfl

def generatorFunctional (poly : ℚ[X] →ₗ[ℚ] ℚ[X]) (pole : ι → ℚ[X]) :
    Data ι →ₗ[ℚ] ℚ[X] :=
  poly.comp (LinearMap.fst ℚ ℚ[X] (ι →₀ ℚ)) +
    (Finsupp.linearCombination ℚ pole).comp (LinearMap.snd ℚ ℚ[X] (ι →₀ ℚ))

def functional (node : ι → ℚ) (hn : Function.Injective node)
    (poly : ℚ[X] →ₗ[ℚ] ℚ[X]) (pole : ι → ℚ[X]) :
    Domain node →ₗ[ℚ] ℚ[X] :=
  (generatorFunctional poly pole).comp (coordinates node hn).symm.toLinearMap

@[simp] theorem functional_ofData (node : ι → ℚ) (hn : Function.Injective node)
    (poly : ℚ[X] →ₗ[ℚ] ℚ[X]) (pole : ι → ℚ[X]) (d : Data ι) :
    functional node hn poly pole (ofData node d) = generatorFunctional poly pole d := by
  change generatorFunctional poly pole ((coordinates node hn).symm (coordinates node hn d)) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem functional_polynomial (node : ι → ℚ) (hn : Function.Injective node)
    (poly : ℚ[X] →ₗ[ℚ] ℚ[X]) (pole : ι → ℚ[X]) (q : ℚ[X]) :
    functional node hn poly pole (ofData node (q,0)) = poly q := by
  simp [generatorFunctional]

@[simp] theorem functional_pole (node : ι → ℚ) (hn : Function.Injective node)
    (poly : ℚ[X] →ₗ[ℚ] ℚ[X]) (pole : ι → ℚ[X]) (a : ι) :
    functional node hn poly pole (ofData node (0,Finsupp.single a 1)) = pole a := by
  simp [generatorFunctional]

/-- Representation independence is a conclusion of rational-function equality. -/
theorem functional_representation_independent (node : ι → ℚ) (hn : Function.Injective node)
    (poly : ℚ[X] →ₗ[ℚ] ℚ[X]) (pole : ι → ℚ[X]) (d e : Data ι)
    (h : realize node d = realize node e) :
    generatorFunctional poly pole d = generatorFunctional poly pole e := by
  exact congrArg (generatorFunctional poly pole) (realize_injective node hn h)

end ManuscriptChain.SimplePole

namespace ManuscriptChain.Tau

abbrev integerNode (r : ℤ) : ℚ := r

lemma integerNode_injective : Function.Injective integerNode := Int.cast_injective

abbrev RationalDomain := SimplePole.Domain integerNode

/-- The actual τ_X of Lemma 2.2 on the subspace of simple integer poles. -/
def rationalFunctional (k : ℕ) : RationalDomain →ₗ[ℚ] ℚ[X] :=
  SimplePole.functional integerNode integerNode_injective
    ((Algebra.linearMap ℚ ℚ[X]).comp (tauPolynomial k)) (tauPolePoly k)

@[simp] theorem rationalFunctional_polynomial (k : ℕ) (q : ℚ[X]) :
    rationalFunctional k (SimplePole.ofData integerNode (q,0)) = C (tauPolynomial k q) := by
  simp [rationalFunctional, SimplePole.generatorFunctional]

@[simp] theorem rationalFunctional_pole (k : ℕ) (r : ℤ) :
    rationalFunctional k (SimplePole.ofData integerNode (0,Finsupp.single r 1)) =
      C (Real.harmonic (2*k+1) (dIndex r)) - X := by
  simp [rationalFunctional, SimplePole.generatorFunctional, tauPolePoly]

/-- The exact rational function underlying an integer-pole domain generator. -/
theorem rationalDomain_pole_coe (r : ℤ) :
    (SimplePole.ofData integerNode (0,Finsupp.single r 1) : RatFunc ℚ) =
      (RatFunc.X - RatFunc.C (r : ℚ))⁻¹ := by
  simp [SimplePole.realize_apply, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

end ManuscriptChain.Tau

namespace ManuscriptChain.Mu

/-- Index `j` represents the paper pole `-(j+1)^2`; every positive square occurs. -/
def squareNode (j : ℕ) : ℚ := -((j+1 : ℕ) : ℚ)^2

lemma squareNode_injective : Function.Injective squareNode := by
  intro a b h
  have ha : (0 : ℚ) ≤ (a+1 : ℕ) := by positivity
  have hb : (0 : ℚ) ≤ (b+1 : ℕ) := by positivity
  have he : ((a+1 : ℕ) : ℚ) = (b+1 : ℕ) := by
    dsimp [squareNode] at h
    nlinarith
  exact Nat.add_right_cancel (by exact_mod_cast he)

abbrev RationalDomain := SimplePole.Domain squareNode

/-- Definition 2.1 as a well-defined functional on actual rational functions. -/
def rationalFunctional (k : ℕ) : RationalDomain →ₗ[ℚ] ℚ[X] :=
  SimplePole.functional squareNode squareNode_injective
    ((Algebra.linearMap ℚ ℚ[X]).comp (Tau.muPolynomial k))
    (fun j => Tau.muPolePoly k (j+1))

@[simp] theorem rationalFunctional_polynomial (k : ℕ) (q : ℚ[X]) :
    rationalFunctional k (SimplePole.ofData squareNode (q,0)) =
      C (Real.polynomialMoment k q) := by
  simp [rationalFunctional, SimplePole.generatorFunctional]

@[simp] theorem rationalFunctional_pole (k j : ℕ) :
    rationalFunctional k (SimplePole.ofData squareNode (0,Finsupp.single j 1)) =
      C (Real.poleConstant k (j+1)) + C (((j+1 : ℕ) : ℚ)^(2*k)) * X := by
  simp [rationalFunctional, SimplePole.generatorFunctional, Tau.muPolePoly_eq_existing]

end ManuscriptChain.Mu
