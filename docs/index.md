---
layout: default
title: Harmonic PDE Principles · Lean 4 讲义
description: 五个 Lean 文件的证明结构、Evans 第二章数学背景与可编辑 Lean 示例
---

<p class="document-meta">Lean 4 / mathlib / 调和函数</p>

# 调和函数最大值原理：从数学证明到 Lean 形式化

<p class="lead">这份极简讲义按“局部常值性 → 强最大值原理 → 边界最大值原理 → 比较原理 → Poisson–Dirichlet 唯一性”组织五个 Lean 文件，并把关键步骤与 Evans《偏微分方程》第 2 章逐一对应。</p>

<div class="quick-links">
  <a href="#proof-map">查看证明地图</a>
  <a href="#five-files">阅读五个文件</a>
  <a href="#evans">核对数学证明</a>
  <a href="#interactive">使用交互代码</a>
  <a href="{{ '/downloads/HarmonicPDEPrinciples2_five_lean_files_guide.pdf' | relative_url }}">下载完整 PDF</a>
</div>

<div class="note"><p><strong>文件保护：</strong>本站是新增文档层，没有覆盖或改写原来的五个 <code>.lean</code> 文件、HTML 或 PDF。后续若要修订既有文稿，将按约定以紫色文字和删除线保留原文痕迹。</p></div>

## 证明地图 {#proof-map}

~~~text
LocalMaximumBall.lean
  球均值性质 + 内部最大点
              │
              ▼
  最大点附近存在常值球
              │
       ┌──────┴─────────┐
       ▼                ▼
ComplexBallMeanValue   BoundaryMaximum
二维调和函数自动满足     水平集在 U 中既开又闭
球均值性质               + U 连通
       │                │
       └──────┬─────────┘
              ▼
      u 在 closure U 上常值
      最大值可移到 frontier U
              │
       ┌──────┴───────────┐
       ▼                  ▼
HarmonicComparison     PoissonDirichletUniqueness
w = u - v             w = u₁ - u₂
边界 w ≤ 0            边界 w = 0
⇒ 闭包 w ≤ 0          ⇒ w = 0
⇒ u ≤ v               ⇒ u₁ = u₂
~~~

数学核心只有两层：

1. **分析层：** 若 \\(u(x_0)\\) 是球内最大值，且
   \\[
   u(x_0)=\frac{1}{|B_r(x_0)|}\int_{B_r(x_0)}u(y)\,dy,
   \\]
   那么连续非负函数 \\(u(x_0)-u(y)\\) 的积分为零，故它在球上恒为零。
2. **拓扑层：** 最大值水平集
   \\[
   A=\{x\in U:u(x)=u(x_0)\}
   \\]
   在相对拓扑中既开又闭；若 \\(U\\) 连通且 \\(A\neq\varnothing\\)，则 \\(A=U\\)。

## 五个文件 {#five-files}

| 文件 | 主要数学命题 | 在证明链中的职责 |
|---|---|---|
| <code>LocalMaximumBall.lean</code> | 内部最大点附近局部常值 | 把均值等式变成局部刚性 |
| <code>ComplexBallMeanValue.lean</code> | \\(E\,2\simeq\mathbb C\\) 下的二维球均值公式 | 为二维版本自动提供均值性质 |
| <code>BoundaryMaximum.lean</code> | 强最大值与边界最大值原理 | 用开闭集和连通性完成全局化 |
| <code>HarmonicComparisonPrinciple.lean</code> | 边界次序推出闭包次序 | 对 \\(u-v\\) 使用最大值原理 |
| <code>PoissonDirichletUniqueness.lean</code> | Poisson–Dirichlet 解至多一个 | 对两个解之差使用零边界结论 |

### 1. LocalMaximumBall.lean

[查看部署后的源码]({{ '/source/LocalMaximumBall.lean' | relative_url }})

文件定义了 \\(E(n)=\mathbb R^n\\)、球体积、球平均值及 <code>HasBallMeanValuePropertyOn</code>。核心定理 <code>exists_ball_eq_const_of_meanValue</code> 的逻辑是：

1. 由 \\(U\\) 开且 \\(x_0\in U\\)，取 \\(r>0\\) 使 \\(\overline B_r(x_0)\subset U\\)。
2. 最大性给出 \\(u(x_0)-u(y)\ge 0\\)。
3. 均值性质给出
   \\[
   \int_{B_r(x_0)}(u(x_0)-u(y))\,dy=0.
   \\]
4. 若某点差值严格为正，连续性会产生一个正测度邻域，使积分严格为正，矛盾。

下面的自包含示例演示第一步；页面加载后代码块可编辑。

~~~lean
import Mathlib

open Metric Set
noncomputable section

namespace LocalMaximumDemo

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def ballVolume {n : ℕ} (x : E n) (r : ℝ) : ℝ :=
  (MeasureTheory.volume (ball x r)).toReal

def HasBallMeanValuePropertyOn {n : ℕ}
    (u : E n → ℝ) (U : Set (E n)) : Prop :=
  ∀ ⦃x : E n⦄, x ∈ U →
    ∀ ⦃r : ℝ⦄, 0 < r → closedBall x r ⊆ U →
      (∫ y in ball x r, u y) = ballVolume x r * u x

example {n : ℕ} {U : Set (E n)} {x₀ : E n}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall x₀ r ⊆ U := by
  rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀) with
    ⟨ε, hε_pos, hεU⟩
  refine ⟨ε / 2, by positivity, ?_⟩
  exact (closedBall_subset_ball (by linarith)).trans hεU

end LocalMaximumDemo
~~~

### 2. ComplexBallMeanValue.lean

[查看部署后的源码]({{ '/source/ComplexBallMeanValue.lean' | relative_url }})

该文件利用实线性等距同构
\\[
\mathbb C\simeq_{\mathbb R}\mathbb R^2
\\]
把 mathlib 中复平面上的圆周均值定理转化为 \\(E\,2\\) 上的圆盘均值定理。关键环节是：

1. 线性等距保持范数、圆与圆盘。
2. 极坐标积分把圆盘积分写为半径与角度的迭代积分。
3. 对每个半径应用调和函数圆周均值公式。
4. 用 \\(|B_r|=\pi r^2\\) 得到
   \\[
   \int_{B_r(x)}u(y)\,dy=\pi r^2u(x).
   \\]

~~~lean
import Mathlib

open Metric Set MeasureTheory
open scoped RealInnerProductSpace
noncomputable section

namespace ComplexBridgeDemo

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev complexToE2 : ℂ ≃ₗᵢ[ℝ] E 2 :=
  Complex.orthonormalBasisOneI.repr

#check Complex.integral_comp_polarCoord_symm
#check HarmonicOnNhd.circleAverage_eq
#check EuclideanSpace.volume_ball_fin_two

example (z : ℂ) : ‖complexToE2 z‖ = ‖z‖ := by
  exact complexToE2.norm_map z

end ComplexBridgeDemo
~~~

### 3. BoundaryMaximum.lean

[查看部署后的源码]({{ '/source/BoundaryMaximum.lean' | relative_url }})

这里最重要的内部对象是：

~~~lean
import Mathlib

open Set

namespace BoundaryDemo

variable {X : Type*} [TopologicalSpace X]

private def maximumLevelSet
    (U : Set X) (u : X → ℝ) (M : ℝ) : Set U :=
  {x | u (x : X) = M}

private lemma maximumLevelSet_closed
    {U : Set X} {u : X → ℝ} {M : ℝ}
    (hu : ContinuousOn u U) :
    IsClosed (maximumLevelSet U u M) := by
  rw [show maximumLevelSet U u M = (U.restrict u) ⁻¹' {M} by
    ext x
    simp [maximumLevelSet]]
  exact isClosed_singleton.preimage hu.restrict

example [PreconnectedSpace X] {A : Set X}
    (hA : IsClopen A) (hne : A.Nonempty) : A = Set.univ :=
  hA.eq_univ hne

end BoundaryDemo
~~~

<code>Set U</code> 是子类型 \\(U\\) 上的集合，所以开闭性是**相对拓扑**中的开闭性。闭性来自
\\[
A=(u|_U)^{-1}(\{M\}),
\\]
而开性来自上一文件的“最大点附近局部常值”。连通性随后迫使 \\(A=U\\)，连续性再把等式从 \\(U\\) 延拓到 \\(\overline U\\)。

为什么用 <code>private def</code> 而不是 <code>def</code>：

1. 该水平集只是当前文件证明强最大值原理的实现细节。
2. <code>private</code> 防止它成为跨文件依赖的公共 API，后续可自由改名或重构。
3. 它不改变定义的数学含义，也不提供额外的逻辑封装；公开定理才是稳定接口。

边界非空还需要 \\(0<n\\)、\\(U\neq\varnothing\\) 和 \\(U\\) 有界。\\(n=0\\) 时 \\(E\,0\\) 是单点空间，全集有界且开，但边界为空，因此维数假设不是形式化噪声。

### 4. HarmonicComparisonPrinciple.lean

[查看部署后的源码]({{ '/source/HarmonicComparisonPrinciple.lean' | relative_url }})

令 \\(w=u-v\\)。调和性对减法封闭，边界条件 \\(u\le v\\) 等价于 \\(w\le0\\)。由于 \\(\overline U\\) 紧且 \\(w\\) 连续，\\(w\\) 取得最大值：

- 若最大点在 \\(\partial U\\)，直接由边界条件得最大值不大于零；
- 若最大点在 \\(U\\)，边界最大值原理把相同最大值移到 \\(\partial U\\)。

故 \\(w\le0\\) 于 \\(\overline U\\)，即 \\(u\le v\\)。

~~~lean
import Mathlib

open Set

namespace ComparisonDemo

variable {X : Type*} [TopologicalSpace X]
variable {U : Set X} {u v : X → ℝ}

def difference (u v : X → ℝ) : X → ℝ := fun x => u x - v x

example (hboundary : ∀ x ∈ frontier U, u x ≤ v x) :
    ∀ x ∈ frontier U, difference u v x ≤ 0 := by
  intro x hx
  dsimp [difference]
  linarith [hboundary x hx]

#check InnerProductSpace.HarmonicContOnCl.sub

end ComparisonDemo
~~~

文件中的 <code>_hΔ : Δu ≤ Δv</code> 没有被证明体使用，因为前提已经说明 \\(u,v\\) 都调和，故两边 Laplacian 均为零。对于一般 \\(C^2\\) 函数，若要由边界 \\(u\le v\\) 推出内部 \\(u\le v\\)，按这里的 Laplacian 号约定应要求 \\(\Delta u\ge\Delta v\\)；不能把这个冗余参数误读成一般比较原理。

### 5. PoissonDirichletUniqueness.lean

[查看部署后的源码]({{ '/source/PoissonDirichletUniqueness.lean' | relative_url }})

若 \\(u_1,u_2\\) 满足同一 Poisson–Dirichlet 问题
\\[
-\Delta u_i=f\quad\text{于 }U,\qquad
u_i=g\quad\text{于 }\partial U,
\\]
则 \\(w=u_1-u_2\\) 满足 \\(\Delta w=0\\) 且 \\(w=0\\) 于边界。先对 \\(w\\) 使用最大值原理得到 \\(w\le0\\)，再对 \\(-w\\) 使用一次得到 \\(w\ge0\\)，故 \\(w=0\\) 于 \\(\overline U\\)。

~~~lean
import Mathlib

open Set

namespace PoissonDemo

variable {X : Type*} [TopologicalSpace X] {U : Set X}
variable {u₁ u₂ g : X → ℝ}

example (h₁ : EqOn u₁ g (frontier U))
    (h₂ : EqOn u₂ g (frontier U)) :
    EqOn (u₁ - u₂) (fun _ => 0) (frontier U) := by
  intro x hx
  simp [h₁ hx, h₂ hx]

example (hzero : ∀ x ∈ U, u₁ x - u₂ x = 0) :
    EqOn u₁ u₂ U := by
  intro x hx
  exact sub_eq_zero.mp (hzero x hx)

#check ContDiffAt.laplacian_sub_nhds

end PoissonDemo
~~~

<code>HasAtMostOnePoissonDirichletSolution</code> 只断言“至多一个解”，不证明解存在。结论使用 <code>EqOn u₁ u₂ (closure U)</code> 而非全局函数相等，因为方程和边界条件没有约束 \\(\overline U\\) 外的函数值。

## 与 Evans 第二章的严格对应 {#evans}

以下证明链对应 Evans, *Partial Differential Equations*, 2nd ed., Chapter 2 中调和函数的均值公式、强最大值原理和 Dirichlet 问题唯一性。

### 定理 A：球均值性质

若 \\(u\in C^2(U)\\) 且 \\(\Delta u=0\\)，对每个 \\(\overline B_r(x)\subset U\\)，有
\\[
u(x)=\frac{1}{|\partial B_r|}\int_{\partial B_r(x)}u\,dS
    =\frac{1}{|B_r|}\int_{B_r(x)}u\,dy.
\\]

严格证明先定义球面平均
\\[
\phi(r)=\frac{1}{|\partial B_r|}\int_{\partial B_r(x)}u\,dS.
\\]
微分并使用散度定理得到
\\[
\phi'(r)=\frac{1}{|\partial B_r|}
          \int_{B_r(x)}\Delta u\,dy=0.
\\]
故 \\(\phi(r)\\) 与 \\(r\\) 无关；令 \\(r\downarrow0\\)，由连续性得 \\(\phi(r)\to u(x)\\)。再对半径积分得到球平均公式。

### 定理 B：强最大值原理

设 \\(U\\) 连通且 \\(u\\) 调和。若存在 \\(x_0\in U\\) 使
\\[
u(x_0)=\max_{\overline U}u,
\\]
则 \\(u\\) 在 \\(U\\) 上恒定。

Lean 文件采用的证明不是沿路径传播常值球，而是更适合形式化的开闭集证明：

1. \\(A=\{x\in U:u(x)=u(x_0)\}\neq\varnothing\\)。
2. \\(u|_U\\) 连续且 \\(\{u(x_0)\}\\) 闭，故 \\(A\\) 闭。
3. 每个 \\(x\in A\\) 也是最大点；定理 A 与非负积分为零推出 \\(u\\) 在 \\(x\\) 附近恒定，故 \\(A\\) 开。
4. \\(U\\) 连通，所以非空开闭集 \\(A=U\\)。

### 定理 C：弱最大值与比较原理

若 \\(U\\) 有界、\\(u\in C(\overline U)\cap C^2(U)\\)、\\(\Delta u=0\\)，则
\\[
\max_{\overline U}u=\max_{\partial U}u.
\\]
若 \\(u\le v\\) 于 \\(\partial U\\) 且两者调和，则对 \\(w=u-v\\) 应用该结论，得到 \\(u\le v\\) 于 \\(\overline U\\)。

### 推论：Dirichlet 唯一性

同一边界数据的两个调和解之差在边界为零；对差及其相反数应用最大值原理，即得二者在闭包上一致。Poisson 方程的情形相同，因为相同右端项相减后成为齐次 Laplace 方程。

<div class="warning"><p><strong>假设检查：</strong>紧性用于保证闭包上的最大值确实被取得；连通性用于把局部常值推广到整个区域；边界非空需排除零维或全集的退化情形。删去这些前提会使对应 Lean 证明和经典命题同时失效。</p></div>

## 交互 Lean 代码 {#interactive}

每个 <code>lean</code> 围栏在浏览器中会变成可编辑代码块：

1. 直接修改代码；按 Tab 插入两个空格。
2. 点击“在 Lean Web 运行”，或按 Ctrl/Command + Enter。
3. “复制”用于转到本地项目；“重置”恢复文档原例。

GitHub Pages 只能托管静态文件，无法在页面服务器上运行 Lean。本站因此把当前代码发送到 Lean 社区的 Lean Web，并固定使用与本项目一致的 <code>mathlib-stable / Lean v4.32.0</code>。完整的五文件项目仍应在本地用 <code>lake build</code> 验证；页面示例全部写成独立的 <code>import Mathlib</code> 小例子。

<div class="warning"><p><strong>执行边界：</strong>只有点击运行或新标签链接时，编辑器内容才会被发送到 <code>live.lean-lang.org</code>。不要在代码块中放入隐私数据或密钥。若站内窗口被浏览器拦截，请使用“新标签打开”。</p></div>

## 重要参考文献

1. L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, Chapter 2：调和函数均值性质、最大值原理与唯一性。
2. D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Springer, Chapters 2–3：椭圆方程的最大值与比较原理。
3. S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, Springer, Chapters 1–2：均值性质与调和函数基础。
4. J. R. Munkres, *Topology*, Pearson：连通空间与开闭集刻画。
5. The mathlib Community, *Mathematics in Lean* 与 mathlib API 文档：子类型拓扑、测度积分及调和函数形式化接口。
