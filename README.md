# The jump set of the one-scale problem for iid linear inequalities

Peiwei Wu and Qian Peng

## The endpoint constant for an extremal iid sum inequality

This companion paper in extremal probability determines the endpoint asymptotics of the largest probability of $X+Y<cZ$ for nonnegative independent and identically distributed random variables. Its exact leading constant is $4/9$. At multinacci numbers, the optimal index range of the quantile-band estimate has order $\sqrt{m\log m}$. Version 1.1.0 includes the Lean 4 proofs.

[Read the endpoint paper (PDF)](https://zenodo.org/records/24614357/files/manuscript.pdf) · [Lean proofs and verification](endpoint-asymptotics/) · [Zenodo DOI](https://doi.org/10.5281/zenodo.24614357) · [BibTeX citation](https://zenodo.org/records/24614357/export/bibtex)

## One-scale paper

[Read the one-scale paper (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Main Lean statements](MainResults.lean) · [Relation to earlier work](PRIORITY.md)

Let the three nonnegative variables X, Y, Z be independent draws from the same law. The one-scale optimum is the supremum of Pr(X+Y<cZ) over laws supported on [a,1] for some a with ca>1. It has infinitely many distinct right jumps in every left neighborhood of the golden ratio. The jump set in (1,φ) is exactly the union of the two interleaved ladder families constructed by Zaytsev and Bellec. Every candidate is a positive jump. Successive jump sizes equal differences of consecutive maxima of an explicit four-mass cubic (starting at three ranks). On each compact subinterval of (1,φ), the optimum has finite range and a finite-support law attains the supremum.

At φ the supremum equals 1/4, and no admissible one-scale law attains it. For 1<c<φ an explicit finite cubic optimization on the ordinary and branching ladder levels gives the exact value.

For the unrestricted optimum S₂(c), the gap 2/3−S₂(c) is of inverse-logarithmic order as c approaches 2 from below. Every left neighborhood of 2 contains infinitely many values of S₂. For each Borel law and 1<c≤φ, writing D=Pr(cX≤Z), its success probability is at most β(c)+2D−D², with the first two uniform coefficients sharp. At φ the separated-scale construction of Zaytsev and Bellec gives S₂(φ) ≥ (√61−5)/6. Proving that S₂ itself has infinitely many discontinuities remains open.

## One-scale proof verification

The project pins Lean 4.19.0 and the published iid-probability formalization at commit `d046e8263df11d71ba9c71a9d16141764558b8fb`, which pins mathlib. With Lean and Lake installed:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true MainResults.lean
```

The last command prints the axiom dependencies of the headline results. The one-scale theorem uses the original Borel-law formulation with support in a compact interval [a,1] satisfying ca>1.

| Theorem | Formal statement |
| --- | --- |
| Exact jump set for the original one-scale Borel problem | `OneScale.original_jump_iff_ladder` |
| Unique roots in order and their golden-ratio limit | `OneScale.rung_root_existsUnique`, `OneScale.rungRoot_strictMono`, `OneScale.rungRoot_tendsto_golden` |
| Exact jump sizes from finite rank maxima | `OneScale.rank_jump_iff`, `OneScale.rankMaximum_strict` |
| Pair-separation bound for arbitrary Borel laws and coefficient optimality | `OneScale.WeightedBridge.iidWin_le_beta_add_spread`, `OneScale.WeightedSharp.coefficients_necessary` |
| One-scale Borel supremum has infinitely many right jumps below the golden ratio | `OneScale.original_one_scale_infinite` |
| Infinite subset of the two explicit candidate families on the original Borel domain | `OneScale.original_ladder_jumps` |
| One-scale value at the golden ratio and its one-sided limits | `OneScale.original_golden_value`, `OneScale.original_tendsto_golden`, `OneScale.original_golden_jump` |
| Explicit finite cubic on the admissible ladder levels and its winning triples | `OneScale.beta_fixed_canonical_menu`, `OneScale.canonical_edge_iff` |
| Nonattainment at the golden ratio for every admissible one-scale Borel law | `OneScale.original_golden_nonattainment` |
| Separated-scale construction and its unrestricted golden-ratio bound | `OneScale.scale_lift`, `OneScale.unrestricted_golden_lower` |
| Two-sided logarithmic estimate for the unrestricted function | `IidInfiniteJumps.inverse_log_bounds` |
| Infinitely many unrestricted function values near 2 | `IidInfiniteJumps.infinitely_many_values` |
| Arbitrarily many jumps near 2 in all sufficiently large finite empirical optima | `IidStaircase.many_finite_jumps_before_two` |

## 中文摘要

三个独立同分布的非负随机变量满足 X+Y<cZ 的最大概率取决于系数 c。当分布集中在一个区间 [a,1] 且 ca>1 时，这个最大概率在 1 与黄金比例之间的全部跳点，恰好是普通阶梯和分支阶梯给出的两族阈值。两个序列交错上升，每个候选点均发生正跳跃，跳幅由两个相邻有限优化问题的最优值之差给出。单尺度上确界在黄金比例处恰为 1/4，且任何允许的分布都无法达到。对允许任意非负分布的原函数，论文给出了接近 2 时的双侧估计和无穷多个不同取值。原函数的跳点总数仍有待确定。

端点论文《独立同分布和式极值概率的端点常数》研究任意非负分布下的精确渐近。它确定了首项常数 $4/9$，并给出分带估计可覆盖的连续候选点数的最优数量级。[论文与正式引用](https://doi.org/10.5281/zenodo.24614357)
