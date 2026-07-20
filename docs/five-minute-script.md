---
layout: default
title: n维欧氏空间调和函数最大值原理的 Lean 4 形式化
description: 汇报稿与核心 Lean 4 代码
permalink: /script/
---

<p class="document-meta">Lean 4</p>

<style>
@media screen and (max-width: 760px) {
  #main-content mjx-container[display="true"] {
    max-width: 100%;
    overflow-x: auto;
    overflow-y: hidden;
  }
}
@media print {
  .skip-link,
  .script-actions {
    display: none !important;
  }
}
</style>

# 调和函数最大值原理的 Lean 4 形式化

<p class="lead">输入输出表和代码放在后半部分，汇报时按需展示。</p>

<div class="quick-links script-actions">
  <a href="#script">正文</a>
  <a href="#input-output">输入与输出</a>
  <a href="#code">关键代码</a>
  <a href="{{ '/downloads/HarmonicPDEPrinciples_five_minute_script.pdf' | relative_url }}">下载 PDF</a>
</div>

## 五分钟汇报正文 {#script}

### 1.　目标与输入输出

调和函数最大值原理的 Lean 4 形式化。

核心局部 API 的输入是：\\(U\subset\mathbb R^n\\) 为开集，\\(x_0\in U\\)；函数 \\(u\\) 在 \\(\overline U\\) 连续，\\(x_0\\) 是闭包上的最大点，并且 \\(u\\) 满足球平均值性质。输出是
\\[
\exists r>0,\qquad
\overline B(x_0,r)\subset U,\qquad
\forall y\in B(x_0,r),\ u(y)=u(x_0).
\\]
因此 Lean 返回的不只是“局部常值”，还包括正半径和闭球包含关系。

### 2.　文件一：局部常值

第一个文件 <code>LocalMaximumBall.lean</code> 建立这个局部定理。空间定义为 <code>EuclideanSpace ℝ (Fin n)</code>，它已经带有距离、内积、拓扑和 Lebesgue 体积；闭包、边界和球直接使用 mathlib。

证明先利用 \\(U\\) 的开性，在 \\(x_0\\) 周围构造闭球包含于 \\(U\\)。令 \\(M=u(x_0)\\)。最大值性质给出 \\(u\le M\\)，均值性质给出
\\[
\int_Bu=|B|M=\int_BM.
\\]
代码由不等式和积分相等得到 \\(u=M\\) 几乎处处，再用连续性提升为球上逐点相等，最终构造出所需的 \\(r\\)。

### 3.　文件二：二维平均值公式

第二个文件 <code>ComplexBallMeanValue.lean</code> 在二维自动生成均值性质。代码利用等距同构 \\(\mathbb C\simeq_{\mathbb R}\mathbb R^2\\)，证明调和性在坐标变换下保持，再结合圆周均值定理和极坐标积分，得到
\\[
\int_{B(c,r)}f(z)\,dz=\pi r^2f(c).
\\]
所以二维调和函数可以直接调用局部常值定理，不需要额外传入 <code>hmean</code>。

### 4.　文件三：强最大值与边界最大值

第三个文件 <code>BoundaryMaximum.lean</code> 把局部常值推广到整个连通区域。定义最大值水平集
\\[
A=\{x\in U\mid u(x)=u(x_0)\}.
\\]
连续性说明 \\(A\\) 在子空间 \\(U\\) 中闭，局部常值定理说明 \\(A\\) 开，而且 \\(x_0\in A\\)。由连通性得到 \\(A=U\\)，再由闭包连续性把等式延伸到 \\(\overline U\\)。

当 \\(n>0\\)、\\(U\\) 非空且有界时，边界非空，因此同一个最大值在边界上达到，并得到
\\[
\sup u(\partial U)=\sup u(\overline U).
\\]

### 5.　文件四：调和函数的比较原理

第四个文件 <code>HarmonicComparisonPrinciple.lean</code> 证明比较原理。若 \\(u,v\\) 调和且边界上 \\(u\le v\\)，令 \\(w=u-v\\)。调和性对减法封闭，所以 \\(w\\) 调和，边界条件变成 \\(w\le0\\)。对 \\(w\\) 使用边界最大值原理，得到
\\[
\forall x\in\overline U,\qquad u(x)\le v(x).
\\]

### 6.　文件五：Poisson–Dirichlet 唯一性

第五个文件 <code>PoissonDirichletUniqueness.lean</code> 封装 \\(C^2(U)\\)、闭包连续性、方程 \\(-\Delta u=f\\) 和边界条件 \\(u=g\\)。

若 \\(u_1,u_2\\) 是同一问题的两个解，令 \\(w=u_1-u_2\\)。相同右端项使 \\(w\\) 调和，相同边界数据使 \\(w=0\\) 于边界。分别对 \\(w\\) 和 \\(-w\\) 使用最大值原理，得到
\\[
u_1=u_2\qquad\text{于 }\overline U.
\\]
因此该 Poisson–Dirichlet 问题至多有一个经典解。

### 7.　总结与后续工作

五个文件形成以下证明链：

~~~text
满足平均值公式得到在局部球上的结论
  → U上的最大值与边界最大值的关系
  → 二维欧氏空间调和函数的平均值公式（缺少高维情况）
  → 调和函数的比较原理
  → Poisson–Dirichlet 至多有一个经典解
~~~

当前二维版本已经能从调和性自动得到全部结论。下一步是在一般 \\(\mathbb R^n\\) 中形式化球均值定理，消除一般维接口中的 <code>hmean</code>；随后补充均值性质对加法、减法和数乘的自动化，并继续研究 Poisson 解的存在性和 Sobolev 弱解。

我的汇报到这里，谢谢大家。

## 准确输入与输出 {#input-output}

### 局部常值 API

| 类别 | Lean 输入或输出 |
|---|---|
| 输入 | <code>hU_open : IsOpen U</code> |
| 输入 | <code>hu_cont : ContinuousOn u (closure U)</code> |
| 输入 | <code>hx₀ : x₀ ∈ U</code> |
| 输入 | <code>hmax : AttainsMaxOnClosure u U x₀</code> |
| 输入 | <code>hmean : HasBallMeanValuePropertyOn u U</code> |
| 输出 | <code>0 < r</code> |
| 输出 | <code>Metric.closedBall x₀ r ⊆ U</code> |
| 输出 | <code>Set.EqOn u (fun _ => u x₀) (Metric.ball x₀ r)</code> |

### 后续文件

| 文件 | 主要新增输入 | 输出 |
|---|---|---|
| <code>ComplexBallMeanValue.lean</code> | <code>HarmonicOnNhd u U</code>，且 \\(n=2\\) | 自动生成球均值性质 |
| <code>BoundaryMaximum.lean</code> | 连通性；边界结论还需正维、非空和有界 | 闭包常值；边界与闭包最大值相等 |
| <code>HarmonicComparisonPrinciple.lean</code> | \\(u,v\\) 调和；边界 \\(u\le v\\) | \\(u\le v\\) 于 \\(\overline U\\) |
| <code>PoissonDirichletUniqueness.lean</code> | 两个解具有相同 \\(f\\) 和 \\(g\\) | <code>EqOn u₁ u₂ (closure U)</code> |

## 关键 Lean 4 代码 {#code}

### 1. 局部定理的完整接口

~~~text
theorem exists_ball_eq_const_of_meanValue {n : ℕ}
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (hU_open : IsOpen U)
    (hu_cont : ContinuousOn u (closure U))
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall x₀ r ⊆ U ∧
      Set.EqOn u (fun _ : E n => u x₀) (Metric.ball x₀ r)
~~~

- <code>0 < r</code>：半径严格为正；
- <code>closedBall x₀ r ⊆ U</code>：保证均值性质可在该球上使用；
- <code>Set.EqOn</code>：两个函数在指定集合上逐点相等。

### 2. 积分等式到逐点常值

~~~text
have hu_le_M_ae :
    u ≤ᵐ[volume.restrict B] (fun _ : E n => M) := by
  filter_upwards [ae_restrict_mem hB_measurable] with y hy
  exact hmax.2 (subset_closure (hB_U hy))

have hu_eq_M_ae :
    u =ᵐ[volume.restrict B] (fun _ : E n => M) :=
  (integral_eq_iff_of_ae_le
      hu_integrable_B hM_integrable_B hu_le_M_ae).mp
    h_integrals_equal

have hu_eq_M_on_B : Set.EqOn u (fun _ : E n => M) B :=
  volume.eqOn_open_of_ae_eq
    hu_eq_M_ae hB_open hu_B continuousOn_const
~~~

- <code>f =ᵐ[μ] g</code>：在测度 \\(\mu\\) 下几乎处处相等；
- <code>volume.restrict B</code>：把 Lebesgue 测度限制到球 \\(B\\)；
- <code>filter_upwards</code>：组合几乎处处成立的条件。

### 3. 连通性完成全局传播

~~~text
let A : Set U := boundaryMaximumLevelSet U u (u x₀)

have hA_open : IsOpen A := ...
have hA_closed : IsClosed A := ...

letI : PreconnectedSpace U :=
  Subtype.preconnectedSpace hU_preconnected

have hA_univ : A = Set.univ :=
  (show IsClopen A from ⟨hA_closed, hA_open⟩).eq_univ hA_nonempty
~~~

- <code>Set U</code>：子类型 \\(U\\) 上的集合，使用相对拓扑；
- <code>IsClopen A</code>：\\(A\\) 既开又闭；
- <code>letI</code>：在当前证明中安装预连通空间实例；
- <code>private</code>：内部辅助定义不作为项目的公开 API。

## 参考文献

1. L. C. Evans, *Partial Differential Equations*, 2nd ed., Chapter 2。
2. S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, Chapter 1。
3. D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Chapter 3。
