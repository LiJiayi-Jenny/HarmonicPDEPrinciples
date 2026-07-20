---
layout: default
title: 五分钟汇报 · 调和函数最大值原理的 Lean 4 形式化
description: 五个 Lean 文件的精确输入输出、证明流程、关键代码与后续工作
permalink: /five-minute-report/
---

<p class="document-meta">5 分钟口头稿 / 精确 API / Lean 4 代码附录</p>

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
  .report-actions {
    display: none !important;
  }
}
</style>

# 调和函数最大值原理的 Lean 4 形式化

<p class="lead">本材料分为两部分：前半部分是可直接照读的五分钟汇报；后半部分给出每个文件的精确输入、输出、假设用途以及答辩时可展示的关键 Lean 4 代码。</p>

<div class="quick-links report-actions">
  <a href="#oral-script">五分钟口头稿</a>
  <a href="#io-map">输入输出总表</a>
  <a href="#code-appendix">关键代码</a>
  <a href="#future-work">后续工作</a>
  <a href="{{ '/downloads/HarmonicPDEPrinciples_five_minute_report.pdf' | relative_url }}">下载 PDF</a>
</div>

<div class="note"><p><strong>与原总结的关系：</strong>现有 Lean 文件已经正确加入符号条件。本材料修正的是口头表述：不能只说“连续函数积分为零便恒为零”，而应说代码先证明 <code>u ≤ M</code>，再由积分相等得到几乎处处相等，最后用连续性提升为逐点相等。</p></div>

## 首先说清楚命题

### 原始输入并不足够

仅有
\\[
U\subset\mathbb R^n\text{ 为非空、连通、有界开集},\qquad
u\in C^2(U)\cap C(\overline U),
\\]
以及内部最大点 \\(x_0\in U\\)，**不能**推出 \\(u\\) 在 \\(x_0\\) 附近为常数。例如单位球上的
\\[
u(x)=-\lVert x\rVert^2
\\]
在 \\(0\\) 达到最大值，但不局部常值。

因此还必须加入下列条件之一：

1. \\(u\\) 调和，即 \\(\Delta u=0\\)；再由调和性推出球均值性质；
2. 直接把球均值性质作为抽象 API 输入。

### 当前一般维数局部 API

设 \\(E_n=\mathbb R^n\\)。真正用于局部步骤的输入是：

\\[
\begin{aligned}
&U\subset E_n\text{ 为开集},\quad x_0\in U,\\
&u\in C(\overline U),\\
&u(x_0)=\max_{\overline U}u,\\
&\int_{B(x,r)}u(y)\,dy=|B(x,r)|u(x)
  \quad\text{当 }\overline B(x,r)\subset U.
\end{aligned}
\\]

输出是构造一个具体半径：

\\[
\exists r>0,\qquad
\overline B(x_0,r)\subset U,\qquad
\forall y\in B(x_0,r),\ u(y)=u(x_0).
\\]

非空、连通、有界和 \\(C^2\\) 在这个**局部步骤**中不使用：\\(x_0\in U\\) 已保证非空；连通性用于第三个文件的全局传播；有界性用于紧性、最大值存在和边界非空；\\(C^2\\) 或调和性用于产生均值性质。

## 五分钟口头稿 {#oral-script}

### 0:00–0:35　目标与必要条件

大家好，我汇报的是用 Lean 4 形式化调和函数最大值原理。目标是：函数若在区域内部达到闭包最大值，则在某个小球内为常数。仅有 \\(C^2\\) 和内部最大点并不足够，还必须假设调和性或球均值性质。代码以均值性质建立一般维接口，并在二维从调和性自动推出它。

### 0:35–1:35　文件一：局部常值

第一个文件 <code>LocalMaximumBall.lean</code> 证明局部常值。空间取 <code>EuclideanSpace ℝ (Fin n)</code>，球和闭包直接使用 mathlib。由 \\(U\\) 开且 \\(x_0\in U\\)，先取包含于 \\(U\\) 的 \\(\varepsilon\\)-球，再令 \\(r=\varepsilon/2\\)，得到闭球仍在 \\(U\\) 内。令 \\(M=u(x_0)\\)。最大值性质给出 \\(u\le M\\)，均值性质给出
\\[
\int_Bu=|B|M=\int_BM.
\\]
Lean 由不等式和积分相等得到 \\(u=M\\) 几乎处处，再用连续性提升为球上逐点相等。现有代码已经完整处理符号条件。

### 1:35–2:15　文件二：二维均值性质

第二个文件 <code>ComplexBallMeanValue.lean</code> 补齐二维均值定理。它利用等距同构 \\(\mathbb C\simeq\mathbb R^2\\)，证明调和性在坐标变换下保持，再结合圆周均值定理和极坐标换元得到
\\[
\int_{B(c,r)}f(z)\,dz=\pi r^2f(c).
\\]
所以 \\(n=2\\) 时不再需要手工传入 <code>hmean</code>。

### 2:15–3:05　文件三：强最大值与边界最大值

第三个文件 <code>BoundaryMaximum.lean</code> 定义最大值水平集
\\[
A=\{x\in U:u(x)=u(x_0)\}.
\\]
连续性使 \\(A\\) 在子空间 \\(U\\) 中闭，局部常值定理使它开，并且 \\(x_0\in A\\)。连通性因此给出 \\(A=U\\)，闭包连续性再把常值性延伸到 \\(\overline U\\)。结合正维、非空和有界，可证明边界非空，最终得到边界最大值等于闭包最大值。<code>private</code> 只隐藏水平集这一内部实现。

### 3:05–3:43　文件四：比较原理

第四个文件 <code>HarmonicComparisonPrinciple.lean</code> 令 \\(w=u-v\\)。调和性对减法封闭，边界 \\(u\le v\\) 变为 \\(w\le0\\)。对 \\(w\\) 用边界最大值原理，便得到闭包内 \\(u\le v\\)。当前的 \\(\Delta u\le\Delta v\\) 在两函数都调和时是冗余条件；推广到非调和情形时，正确方向应为 \\(\Delta u\ge\Delta v\\)。

### 3:43–4:25　文件五：Poisson–Dirichlet 唯一性

第五个文件 <code>PoissonDirichletUniqueness.lean</code> 封装 \\(C^2\\)、闭包连续、\\(-\Delta u=f\\) 和边界 \\(u=g\\)。对两个解取差 \\(w=u_1-u_2\\)，相同方程使 \\(w\\) 调和，相同边界数据使 \\(w=0\\) 于边界。对 \\(w\\) 和 \\(-w\\) 各用一次最大值原理，得到 \\(w=0\\) 于 \\(\overline U\\)。结论写成闭包上的 <code>EqOn</code>，因为域外没有约束。

### 4:25–5:00　总结与后续

五个文件形成“局部积分论证—二维均值桥梁—强最大值—比较原理—Poisson 唯一性”的证明链。下一步首先在一般 \\(\mathbb R^n\\) 中证明“调和蕴含球均值”，删除临时 <code>hmean</code>；同时精简分层假设并补均值性质的线性运算。之后可研究非调和比较、Poisson 解存在性和 Sobolev 弱解。

## 五文件输入输出总表 {#io-map}

| 文件 | 精确输入 | 精确输出 | 这一层新增的作用 |
|---|---|---|---|
| <code>LocalMaximumBall.lean</code> | <code>IsOpen U</code>；<code>x₀ ∈ U</code>；闭包连续；闭包最大点；球均值性质 | \\(\exists r>0\\)，闭球包含于 \\(U\\)，且 \\(u=u(x_0)\\) 于开球 | 从积分相等得到局部刚性 |
| <code>ComplexBallMeanValue.lean</code> | \\(n=2\\)；<code>HarmonicOnNhd u U</code> | <code>HasBallMeanValuePropertyOn u U</code> | 用复平面圆周均值和极坐标消除二维 <code>hmean</code> |
| <code>BoundaryMaximum.lean</code> | \\(n>0\\)；非空、预连通、有界、开；调和且闭包连续；内部最大点；一般维还需 <code>hmean</code> | \\(u\\) 在闭包常值；边界达到同一最大值；两侧 <code>sSup</code> 相等 | 用最大值水平集的开闭性完成全局传播 |
| <code>HarmonicComparisonPrinciple.lean</code> | 上述区域条件；\\(u,v\\) 调和且闭包连续；边界 \\(u\le v\\)；一般维需 \\(u-v\\) 的 <code>hmean</code> | \\(\forall x\in\overline U,\ u(x)\le v(x)\\) | 对差函数使用弱边界最大值原理 |
| <code>PoissonDirichletUniqueness.lean</code> | 上述区域条件；两个 \\(C^2(U)\cap C(\overline U)\\) 解满足相同 \\(-\Delta u=f\\) 和 \\(u=g\\)；一般维需调和均值提供器 | <code>EqOn u₁ u₂ (closure U)</code>，即至多一个解 | 对两解之差及其负函数各用一次最大值原理 |

### 假设究竟在哪一步使用

| 假设 | 使用位置 |
|---|---|
| <code>IsOpen U</code> 与 <code>x₀ ∈ U</code> | 构造 \\(r>0\\) 及 \\(\overline B(x_0,r)\subset U\\) |
| <code>AttainsMaxOnClosure</code> | 给出球内 \\(u(y)\le u(x_0)\\) |
| <code>HasBallMeanValuePropertyOn</code> | 给出 \\(\int_Bu=|B|u(x_0)\\) |
| 闭包上的连续性 | 球上可积，并把 a.e. 相等提升为逐点相等；最后延拓到闭包 |
| <code>IsPreconnected U</code> | 非空开闭水平集等于整个 \\(U\\) |
| 有界性 | 有限维空间中使 \\(\overline U\\) 紧；比较原理中保证最大值存在 |
| \\(0<n\\)、非空和有界 | 排除 \\(U=\mathbb R^n\\)，保证 <code>frontier U</code> 非空 |
| \\(C^2\\) / 调和性 | 产生 Laplacian 方程和均值性质；不是局部积分论证本身的额外需要 |

## 关键 Lean 4 代码附录 {#code-appendix}

以下是项目代码摘录，需要在项目已有的 import 和 <code>StrongMaximumPrinciple</code> 命名空间中使用。

### 1. 空间、最大值和均值接口

~~~text
-- E n 就是 ℝⁿ；该类型已带距离、范数、内积、拓扑和 Lebesgue 体积。
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

-- 输入“x₀ 在 closure U 上达到最大值”：
-- 第一项记录 x₀∈closure U，第二项是 ∀ y∈closure U, u y≤u x₀。
def AttainsMaxOnClosure
    (u : E n → ℝ) (U : Set (E n)) (x₀ : E n) : Prop :=
  x₀ ∈ closure U ∧ IsMaxOn u (closure U) x₀

-- 使用无除法形式的均值性质，避免每次证明 |B|≠0 后再约分。
def HasBallMeanValuePropertyOn
    (u : E n → ℝ) (U : Set (E n)) : Prop :=
  ∀ ⦃x : E n⦄, x ∈ U →
    ∀ ⦃r : ℝ⦄, 0 < r → Metric.closedBall x r ⊆ U →
      (∫ y in Metric.ball x r, u y) = ballVolume x r * u x
~~~

### 2. 局部 API 的准确输出

~~~text
theorem exists_ball_eq_const_of_meanValue
    {U : Set (E n)} {u : E n → ℝ} {x₀ : E n}
    (hU_open : IsOpen U)
    (hu_cont : ContinuousOn u (closure U))
    (hx₀ : x₀ ∈ U)
    (hmax : AttainsMaxOnClosure u U x₀)
    (hmean : HasBallMeanValuePropertyOn u U) :
    ∃ r : ℝ,
      0 < r ∧                                  -- 半径严格为正
      Metric.closedBall x₀ r ⊆ U ∧             -- 可合法使用 U 上均值性质
      Set.EqOn u (fun _ : E n => u x₀)         -- 函数等于常数 u x₀
        (Metric.ball x₀ r)
~~~

<code>Set.EqOn f g S</code> 表示 \\(\forall x\in S,\ f(x)=g(x)\\)。这里输出的是开球上的常值性，同时额外返回闭球包含关系，便于后续定理继续使用。

### 3. 开集给出小闭球，不需要用 Filter 定义球

~~~text
lemma exists_closedBall_subset_of_isOpen
    (hU_open : IsOpen U) (hx₀ : x₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall x₀ r ⊆ U := by
  rcases Metric.mem_nhds_iff.mp (hU_open.mem_nhds hx₀) with
    ⟨ε, hε_pos, hεU⟩
  refine ⟨ε / 2, by positivity, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith)).trans hεU
~~~

<code>Metric.mem_nhds_iff</code> 把“\\(U\\) 是 \\(x_0\\) 的邻域”展开成“存在一个开球包含于 \\(U\\)”。Filter 在这里表达邻域，但 <code>Metric.ball</code> 本身只是集合，不需要 Filter 来定义。

### 4. 现有代码中的符号条件与 a.e. 到逐点的提升

~~~text
-- 最大值性质先给出 u≤M，因而这里不是任意的零积分连续函数。
have hu_le_M_ae :
    u ≤ᵐ[volume.restrict B] (fun _ : E n => M) := by
  filter_upwards [ae_restrict_mem hB_measurable] with y hy
  exact hmax.2 (subset_closure (hB_U hy))

-- u≤M 且二者积分相等，因此 u=M 几乎处处。
have hu_eq_M_ae :
    u =ᵐ[volume.restrict B] (fun _ : E n => M) :=
  (integral_eq_iff_of_ae_le
      hu_integrable_B hM_integrable_B hu_le_M_ae).mp
    h_integrals_equal

-- u 和常函数都连续；在开球上的 a.e. 相等提升为逐点相等。
have hu_eq_M_on_B : Set.EqOn u (fun _ : E n => M) B :=
  volume.eqOn_open_of_ae_eq
    hu_eq_M_ae hB_open hu_B continuousOn_const
~~~

记号 <code>f =ᵐ[μ] g</code> 表示 \\(f=g\\) 在测度 \\(\mu\\) 下几乎处处；<code>volume.restrict B</code> 是把 Lebesgue 测度限制到球 \\(B\\)；<code>filter_upwards</code> 用于组合“最终成立”或“几乎处处成立”的事实。

### 5. 强最大值原理的开闭集核心

~~~text
-- Set U 是子类型 U 上的集合，因此以下开闭性都是相对拓扑意义。
let A : Set U := boundaryMaximumLevelSet U u (u x₀)

have hA_open : IsOpen A := by
  simpa [A] using
    isOpen_boundaryMaximumLevelSet_of_meanValue
      hU_open hu_cont hmax hmean

have hA_closed : IsClosed A := by
  simpa [A] using
    isClosed_boundaryMaximumLevelSet
      (hu_cont.mono subset_closure)

letI : PreconnectedSpace U :=
  Subtype.preconnectedSpace hU_preconnected

have hA_univ : A = Set.univ :=
  (show IsClopen A from ⟨hA_closed, hA_open⟩).eq_univ hA_nonempty
~~~

<code>letI</code> 在当前证明局部安装一个类型类实例，使 Lean 可以直接使用“预连通空间中的非空开闭集等于全集”。<code>private</code> 使水平集定义只在本文件可见，避免它成为外部依赖的公共 API。

### 6. 比较原理与 Poisson 唯一性的差函数

~~~text
-- 比较原理：w=u-v，边界 u≤v 变为 w≤0。
have hw : InnerProductSpace.HarmonicContOnCl (u - v) U :=
  hu.sub hv
have hw_frontier : ∀ x ∈ frontier U, (u - v) x ≤ 0 := by
  intro x hx
  simp only [Pi.sub_apply]
  linarith [huv_frontier x hx]

-- Poisson 唯一性：相同方程和边界数据使 w 调和且边界为零。
let w : E n → ℝ := u₁ - u₂
have hw : InnerProductSpace.HarmonicContOnCl w U := by
  simpa [w] using
    harmonicContOnCl_sub_of_poissonSolutions hU_open hu₁ hu₂
have hw_zero : Set.EqOn w (fun _ : E n => 0) (frontier U) := by
  simpa [w] using
    sub_eq_zero_on_frontier_of_poissonSolutions hu₁ hu₂
~~~

## 常用函数与操作备注

| Lean 表达式 | 数学含义或作用 |
|---|---|
| <code>closure U</code> | 闭包 \\(\overline U\\) |
| <code>frontier U</code> | 边界 \\(\partial U\\) |
| <code>Metric.ball x r</code> / <code>closedBall x r</code> | 开球 / 闭球 |
| <code>ContinuousOn u S</code> | \\(u\\) 在集合 \\(S\\) 上连续 |
| <code>ContDiffOn ℝ 2 u U</code> | \\(u\in C^2(U)\\) |
| <code>HarmonicContOnCl u U</code> | \\(u\\) 在 \\(U\\) 邻域意义下调和，并在 \\(\overline U\\) 连续 |
| <code>IsMaxOn u S x₀</code> | \\(x_0\\) 的函数值控制 \\(S\\) 上全部函数值；不单独保证 \\(x_0\in S\\) |
| <code>IsGreatest (u '' S) M</code> | \\(M\\) 是像集中的实际最大元，既被达到又是上界 |
| <code>Set.EqOn f g S</code> | \\(f=g\\) 于 \\(S\\)，不声称环境空间上处处相等 |
| <code>f =ᵐ[μ] g</code> | \\(f=g\\) 在测度 \\(\mu\\) 下几乎处处 |
| <code>hu.sub hv</code> / <code>hv.neg</code> | 调和且闭包连续这一性质对减法 / 取负封闭 |
| <code>simpa [...] using h</code> | 用指定化简规则把已有命题 <code>h</code> 改写成当前目标 |
| <code>linarith</code> | 自动处理线性等式与不等式推理 |

## 后续工作 {#future-work}

### P0：近期可完成

1. **分层精简假设。** 保留现有兼容 API，新增真正最小的局部版本；明确开性、连通性、闭包连续性和有界性分别在哪一层出现。
2. **补均值性质的线性运算。** 为 <code>zero</code>、<code>neg</code>、<code>add</code>、<code>sub</code>、<code>smul</code> 建立引理，使比较原理可由 \\(u,v\\) 的均值性质自动构造 \\(u-v\\) 的均值性质。

### P1：中期核心

3. **一般 \\(n\\) 维球均值定理。** 目标是证明
   \\[
   0<n,\quad \operatorname{HarmonicOnNhd}(u,U)
   \Longrightarrow \operatorname{HasBallMeanValuePropertyOn}(u,U).
   \\]
   主要技术瓶颈是一般维球面测度、极坐标分解，或者球上的 Green/Gauss 公式，而不是当前最大值原理的后端证明。
4. **移除一般维 API 的临时 <code>hmean</code>。** 第 3 项完成后，在局部常值、边界最大值、比较和 Poisson 唯一性内部自动生成均值性质；仍可保留抽象的带 <code>hmean</code> 底层定理。

### P2：研究性扩展

5. **非调和比较原理与存在性。** 先实现次调和/上调和函数的正确 Laplacian 符号版本，再证明球上的 Poisson 核存在性，之后考虑一般域的 Perron 方法。
6. **弱解版本。** 对 \\(H^1\\) 或 \\(H_0^1\\) 弱解使用能量法；结论应改为几乎处处相等，边界条件也应使用迹而不是 <code>EqOn frontier</code>。这一方向依赖 Sobolev 空间、迹、Poincaré 不等式及测试函数密度，工作量明显更大。

建议路线：

~~~text
精简假设与线性 API
        ↓
一般 n 维球均值定理
        ↓
删除所有一般维临时 hmean
        ↓
非调和比较 / Poisson 存在性
        ↓
Sobolev 弱解与一般椭圆算子
~~~

## 重要参考文献

1. L. C. Evans, *Partial Differential Equations*, 2nd ed., Chapter 2：调和函数均值公式、强最大值原理、比较与唯一性；Chapter 6：弱解与能量法。
2. S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Chapter 1：调和函数均值性质与最大值原理。
3. D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Chapter 3：经典最大值原理；Chapter 8：广义解相关理论。
4. Lean 实现直接使用 mathlib 的复调和均值、内积空间 Laplacian、Lebesgue 积分、极坐标换元及连通拓扑模块。
