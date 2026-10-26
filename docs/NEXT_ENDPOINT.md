# Next single-target handoff — following P05.02(2) finite Krein checkpoint

## Newly completed, PASS-ONCE frozen

- `P05_02_2_FINITE_KREIN`: actual ζ7 **monomial** double Beukers integral is exactly its signed 1/1440 Krein mode sum. The same exact moments admit a finite rational polynomial coefficient bilinear extension.
- [PR #29](https://github.com/randogelist/snditeration/pull/29) merged 588230a857acb5a8b74b76ecf99686e79925759c. [Lean 4.33 CI 40271072845](https://github.com/randogelist/snditeration/actions/runs/40271072845) PASS, 8,798 jobs, standard-only axioms in six requested declarations, placeholder scan PASS. Verified source head 372deda8edc77bba6312b8f80137e00e1b75e74f.
- All preexisting proof modules and Mathlib `.olean` cache assumptions are preserved. Source blobs for both new modules and root/audit entry points match between passing proof head and merged main.

## Next mathematical target — NOT STARTED

`P05_02_2_GENERAL_L2_BEUKERS_KREIN`: finish the **original** Theorem 5.2(2), which quantifies over arbitrary f∈L²(0,1), not merely monomials.

1. Prove finite polynomial expansion equals the **single actual double integral** of f(x1)g(x2) against `Beukers.density` (the frozen `polynomialMomentForm` is currently defined as finite sum of individually integrated monomial moments). Establish integrability and finite integration linearity.
2. Interchange the finite polynomial coefficients with the **infinite** signed mode sum and show that the mode coefficients equal actual integrals of f(x)x^m(-log x)^ν. All nonnegative/absolute summability premises must be proved, not assumed.
3. Extend both sides continuously from polynomial functions to arbitrary f∈L²(0,1); prove kernel Hilbert–Schmidt/absolute boundedness and uniform signed-mode norm tails to pass the limit.
4. Recompile and axiom-audit the exact L² theorem with Lean 4.33 and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. The infinite positive/negative polynomial cones of 5.2(3) remain a **separate** mathematical problem; do not assume away the Krein negative tail.

Parallel branches and unrelated PRs may run independently, but no extra theorem has been started in this handoff.

No claim of ζ7 irrationality, full printed 5.2(2), RH or S-Tier is made.
