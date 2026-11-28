# The endpoint constant for an extremal iid sum inequality

**Peiwei Wu and Qian Peng** · November 28, 2026 · Preprint, version 1.1.0

[Paper (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Lean theorem index](EndpointAsymptotics.lean) · [Zenodo archive](https://doi.org/10.5281/zenodo.24614357)

Let $X,Y,Z$ be independent with a common Borel probability law on $[0,\infty)$, and let $S_2(c)$ be the supremum of $\Pr(X+Y<cZ)$ over these laws. We determine the exact rate at which the unrestricted probability approaches $2/3$:

$$
\lim_{c\uparrow 2}\frac{-\log(2-c)}{\log c}\left(\frac23-S_2(c)\right)=\frac49.
$$

The proof gives an upper bound for arbitrary laws and matches it to first order by optimizing the masses of a finite ladder. At the multinacci coefficient $c_m\in(1,2)$ satisfying $(2-c_m)c_m^m=1$, splitting each ladder site into two nearby atoms gives a positive correction of at least $\log(m-3)/(1000m^2)$ above $2/3-4/(9m)$ for all sufficiently large $m$.

Version 1.1.0 determines how far the upper bound at one multinacci coefficient can be carried across later coefficients by the band estimate of Proposition 2.1. The largest index offset for a direct application is of order $\sqrt{m\log m}$. Proposition 2.4 gives explicit bounds in both directions. Allowing an estimate at a later coefficient and transferring it back by monotonicity gives the same order. Throughout the guaranteed range, the values of $S_2$ and their right limits share a bound strictly below the comparison bound at the starting coefficient. [Previous version](https://doi.org/10.5281/zenodo.24614075)

The question of infinitely many discontinuities of the unrestricted $S_2$ remains open. Zaytsev and Bellec formulated the question and constructed the underlying ladder thresholds. Our earlier paper proved inverse-logarithmic order at the endpoint and classified the jumps of the one-scale model. [Original question, §7.1.3](https://arxiv.org/html/2611.29223v1#S7.SS1.SSS3) · [Earlier one-scale paper](https://github.com/PEIWEIWU-AYS/one-scale-iid-probability-jumps-golden-ratio/releases/tag/v1.0.0)

## Proofs

| Result | Lean declaration |
| --- | --- |
| Exact endpoint limit for the unrestricted supremum | `MultinacciBands.population_endpoint_limit` |
| Explicit population upper bound at the multinacci coefficients | `MultinacciBands.unrestricted_upper` |
| Positive logarithmic correction from splitting the sites | `FullRankWindow.positive_logarithmic_population_correction` |
| Lower bound on the number of sites in an improving finite weak block | `FullRankWindow.threshold_witness_log_excess` |
| Eventual strict improvement over every fixed number of additional ranks | `FullRankWindow.threshold_beats_fixed_ceilings` |

| Result added in version 1.1.0 | Lean declaration |
| --- | --- |
| Uniform strict improvement over the comparison bound on an explicit right interval | `MultinacciBands.explicit_right_interval_strict_cap` |
| Uniform bound through a logarithmic number of consecutive candidate coefficients | `MultinacciBands.logarithmic_run_strict_cap` |
| Explicit construction covering every offset with $4j^2 \le m d_m$ | `MultinacciBands.square_root_band_reach` |
| Upper bound on the reach of any direct application of Proposition 2.1 | `MultinacciBands.band_reach_upper` |
| Existence and two-sided bounds for the maximum offset, allowing transfer by monotonicity | `MultinacciBands.optimal_band_reach` |

Here $d_m=\lceil \log(4m)/\log(3/2)\rceil$. A candidate is a multinacci coefficient at which a finite model can change. The existence of a jump for the unrestricted probability at that coefficient is a separate question.

## Reproduce the verification

Install Lean via elan and make Python 3 available. Run the following commands in the directory containing this README and `lakefile.toml`. Lake uses the versions in `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
lake env python3 tools/verify.py
```

The verifier recompiles the research modules from source one at a time and checks the axiom dependencies of the results in the theorem index. The toolchain is Lean 4.19.0. The two preceding formalizations and mathlib are pinned to public Git revisions. [Verification output](AXIOMS.txt)

## Citation

Peiwei Wu and Qian Peng (2026). *The endpoint constant for an extremal iid sum inequality*. Version 1.1.0. Zenodo. [doi:10.5281/zenodo.24614357](https://doi.org/10.5281/zenodo.24614357)

Qian Peng is the corresponding author. The authors' contributions to this archive are distributed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). External dependencies carry their own licenses.
