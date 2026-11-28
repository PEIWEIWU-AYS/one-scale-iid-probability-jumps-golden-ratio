# The endpoint constant for an extremal iid sum inequality

**Peiwei Wu and Qian Peng** · November 28, 2026 · Preprint, version 1.0.0

[Paper (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Lean theorem index](EndpointAsymptotics.lean) · [Zenodo archive](https://doi.org/10.5281/zenodo.24614075)

Let $X,Y,Z$ be independent with a common Borel probability law on $[0,\infty)$, and let $S_2(c)$ be the supremum of $\Pr(X+Y<cZ)$ over these laws. We determine the exact rate at which the unrestricted probability approaches $2/3$:

$$
\lim_{c\uparrow 2}\frac{-\log(2-c)}{\log c}\left(\frac23-S_2(c)\right)=\frac49.
$$

The proof gives an upper bound for arbitrary laws and matches it to first order by optimizing the masses of a finite ladder. At the multinacci coefficient $c_m\in(1,2)$ satisfying $(2-c_m)c_m^m=1$, splitting each ladder site into two nearby atoms gives a positive correction of at least $\log(m-3)/(1000m^2)$ above $2/3-4/(9m)$ for all sufficiently large $m$.

The question of infinitely many discontinuities of the unrestricted $S_2$ remains open. Zaytsev and Bellec formulated the question and constructed the underlying ladder thresholds. Our earlier paper proved inverse-logarithmic order at the endpoint and classified the jumps of the one-scale model. [Original question, §7.1.3](https://arxiv.org/html/2611.29223v1#S7.SS1.SSS3) · [Earlier one-scale paper](https://github.com/PEIWEIWU-AYS/one-scale-iid-probability-jumps-golden-ratio/releases/tag/v1.0.0)

## Proofs

| Result | Lean declaration |
| --- | --- |
| Exact endpoint limit for the unrestricted supremum | `MultinacciBands.population_endpoint_limit` |
| Explicit population upper bound at the multinacci coefficients | `MultinacciBands.unrestricted_upper` |
| Positive logarithmic correction from splitting the sites | `FullRankWindow.positive_logarithmic_population_correction` |
| Lower bound on the number of sites in an improving finite weak block | `FullRankWindow.threshold_witness_log_excess` |
| Eventual strict improvement over every fixed number of additional ranks | `FullRankWindow.threshold_beats_fixed_ceilings` |

## Reproduce the verification

Install Lean via elan and make Python 3 available. Run the following commands in the directory containing this README and `lakefile.toml`. Lake uses the versions in `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
lake env python3 tools/verify.py
```

The verifier recompiles the research modules from source one at a time and checks the axiom dependencies of the five results above. The toolchain is Lean 4.19.0. The two preceding formalizations and mathlib are pinned to public Git revisions. [Verification output](AXIOMS.txt)

## Citation

Peiwei Wu and Qian Peng (2026). *The endpoint constant for an extremal iid sum inequality*. Version 1.0.0. Zenodo. [doi:10.5281/zenodo.24614075](https://doi.org/10.5281/zenodo.24614075)

Qian Peng is the corresponding author. The authors' contributions to this archive are distributed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). External dependencies carry their own licenses.
