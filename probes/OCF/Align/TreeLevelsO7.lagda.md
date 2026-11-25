# TreeLevels O7：raw 扩张的三路必要条件（部分完成）

本篇是第 4 层的否定探针，不是成品构造。目标是把“需要派发”改写成
关于折叠方程本身的条件定理。它不假定比较器、派发完备性、输出反射，
也不假定任意两棵可数层号树可比。

输入是以现有 `Level.Ordᶜ j` 为低层分支域的严格正 raw 树扩张 `TΩ+1`。
另设的位置载体 `Layer` 把所有 `lower j` 放进符号 Ω+1 的共同作用域；
`Common` 只记录这个 raw 扩张签名的共同作用域证据，并未实现为某棵
合法高层树的字面第一位置。`Layer.Ω` 与实际输入构造子
`TΩ+1.nodeΩ+1` 的分支域 `TΩ` 之间也还没有位置嵌入或内部 View 的桥。
所以名称 Ω+1 不认证这个载体的序数值或合法性，不能把 `Common`
当作已有候选的合法公共界。

接口要求三条律：低于目标时保留 Ω 根，同层时取链，在上时取链。
链用接口自身的折叠输出回灌，不另加一个比较器。**O7 状态为部分完成：**
raw 扩张上的三路必要条件已经编译，合法公共界及内部 View 的桥未证，
还没有实例化到任何现有候选。

关键区别：`Stage2.aₛ` 在开关后只把 n 换成 n+1，所得层号与 ω+1
可能不可比，单凭原序列不能应用“在上”律。本篇复用 `Stage2.any`、
`any-false`、`any-true`，把开关后的项换成 ω+2。这样恒假时层号
与 ω 结构互模拟，出现真值时 ω+1 是其字面前驱。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO7 where

open import Data.Nat using (ℕ)
import Data.Nat as N
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import OCF.Align.Level as L
import OCF.Align.Stage2 as S

data Layer : Set where
  lower : L.Ordᴵ → Layer
  Ω Ω+1 : Layer

data _◁_ : Layer → Layer → Set where
  belowΩ : ∀ j → lower j ◁ Ω
  belowΩ+1 : ∀ {x} → x ◁ Ω → x ◁ Ω+1
  Ω-below : Ω ◁ Ω+1

Common : L.Ordᴵ → L.Ordᴵ → Set
Common i j = (lower i ◁ Ω+1) × (lower j ◁ Ω+1)

common : ∀ i j → Common i j
common i j = belowΩ+1 (belowΩ i) , belowΩ+1 (belowΩ j)

data TΩ : Set where
  zΩ : TΩ
  sΩ : TΩ → TΩ
  lΩ : (ℕ → TΩ) → TΩ
  nodeΩ : (j : L.Ordᴵ) → (L.Ordᶜ j → TΩ) → TΩ

data TΩ+1 : Set where
  z : TΩ+1
  s : TΩ+1 → TΩ+1
  l : (ℕ → TΩ+1) → TΩ+1
  node : (j : L.Ordᴵ) → lower j ◁ Ω+1 → (L.Ordᶜ j → TΩ+1) → TΩ+1
  nodeΩ+1 : (TΩ → TΩ+1) → TΩ+1

at : (j : L.Ordᴵ) → (L.Ordᶜ j → TΩ+1) → TΩ+1
at j f = node j (belowΩ+1 (belowΩ j)) f

Fold : Set
Fold = (i : L.Ordᴵ) → TΩ+1 → L.Ordᶜ i

iter : ∀ {A : Set} → (A → A) → A → ℕ → A
iter f a N.zero = a
iter f a (N.suc n) = f (iter f a n)

γ : Fold → (j : L.Ordᴵ) → (L.Ordᶜ j → TΩ+1) → ℕ → L.Ordᶜ j
γ F j f = iter (λ x → F j (f x)) (L.Ω j)

chain : Fold → (i j : L.Ordᴵ) → (L.Ordᶜ j → TΩ+1) → L.Ordᶜ i
chain F i j f = L.lim (λ n → F i (f (γ F j f n)))

record ThreeEquations : Set₁ where
  field
    F : Fold
    keep : ∀ i j → Common i j → (f : L.Ordᶜ j → TΩ+1) → j L.≺ᴵ i →
      Σ[ j′ ∈ L.Ordᴵ ] Σ[ e ∈ j L.≅ᴵ j′ ] Σ[ p ∈ j′ L.<ᴵ i ]
        F i (at j f) ≡
          L.limᵢ p (λ y → F i (f (L.tr⁻ e (L.out (L.<→◃ p) y))))
    same : ∀ i j → Common i j → (f : L.Ordᶜ j → TΩ+1) → j L.≅ᴵ i →
      F i (at j f) ≡ chain F i j f
    above : ∀ i j → Common i j → (f : L.Ordᶜ j → TΩ+1) → i L.≺ᴵ j →
      F i (at j f) ≡ chain F i j f
```

`keep` 的代表元、搬运和输出分支逐字对应现有 `Level.ψ` 的保留行。
这里允许接口选一个代表元，未要求不同位置证明字面相等。同层、在上两行
与现有链公式同形。尚未要求零、后继、ℕ-极限或顶层 Ω 结点的方程；
所以后面的结论也适用于另行满足这些方程的完整折叠。

## 只观察真实输出的根

`Ω-root` 区分 Ω 结点与其它根。它不读取节点的坐标，不判等，不反推
输入层号的关系。`RootDispatch` 是三路方程的一个较弱后果。

```agda
Ω-root : ∀ {i} → L.Ordᶜ i → Bool
Ω-root L.zero = false
Ω-root (L.suc x) = false
Ω-root (L.lim f) = false
Ω-root (L.limᵢ p f) = true
Ω-root (L.up r x) = false

record RootDispatch (δ : L.Ordᴵ) : Set where
  field
    root : L.Ordᴵ → Bool
    root-keep : ∀ j → Common δ j → j L.≺ᴵ δ → root j ≡ true
    root-same : ∀ j → Common δ j → j L.≅ᴵ δ → root j ≡ false
    root-above : ∀ j → Common δ j → δ L.≺ᴵ j → root j ≡ false

equations→roots : ThreeEquations → ∀ δ → RootDispatch δ
equations→roots E δ = record
  { root = λ j → Ω-root (F δ (at j (λ _ → z)))
  ; root-keep = keep-root
  ; root-same = λ j b e → cong Ω-root (same δ j b (λ _ → z) e)
  ; root-above = λ j b p → cong Ω-root (above δ j b (λ _ → z) p)
  }
  where
  open ThreeEquations E
  keep-root : ∀ j → Common δ j → j L.≺ᴵ δ → Ω-root (F δ (at j (λ _ → z))) ≡ true
  keep-root j b p with keep δ j b (λ _ → z) p
  ... | j′ , e , q , eq = cong Ω-root eq
```

## 放大的开关序列

以下层号仍在现有 `Ordᴵ` 内。所有序列步进都显式给出；没有假定
严格增列，也没有从层号的序数值推出关系。

```agda
δ : L.Ordᴵ
δ = L.suc L.ωᴵ

sw : Bool → ℕ → L.Ordᴵ
sw false n = L.natᴵ n
sw true n = L.suc δ

sw-step : ∀ b c n → sw b n L.⊑ᴵ sw (b ∨ c) (N.suc n)
sw-step true c n = L.⊑ᴵ-refl
sw-step false true n = L.Sim→⊑ᴵ (λ q → L.suc (L.suc (L.lim n q)))
sw-step false false n = L.natᴵ-step n

switch : (ℕ → Bool) → L.Ordᴵ
switch α = L.lim (λ n → sw (S.any α n) n)
  (λ n → sw-step (S.any α n) (α (N.suc n)) n)

switch-off : ∀ α → (∀ n → α n ≡ false) → switch α L.≅ᴵ L.ωᴵ
switch-off α h = L.l≅ (λ n →
  subst (λ b → sw b n L.≅ᴵ L.natᴵ n) (sym (S.any-false h n)) (L.≅ᴵ-refl _))

switch-below : ∀ α → (∀ n → α n ≡ false) → switch α L.≺ᴵ δ
switch-below α h = L.via (switch-off α h) L.zero

switch-on : ∀ α n → α n ≡ true → δ L.≺ᴵ switch α
switch-on α n e = L.via (L.≅ᴵ-refl δ) (L.lim n
  (subst (λ b → δ L.<ᴵ sw b n) (sym (S.any-true n e)) L.zero))

true≢false : ¬ (true ≡ false)
true≢false ()

roots→WLPO : RootDispatch δ → S.WLPO
roots→WLPO D α with RootDispatch.root D (switch α) in eq
... | true = inj₁ all-false
  where
  open RootDispatch D
  all-false : ∀ n → α n ≡ false
  all-false n with α n in en
  ... | false = refl
  ... | true = ⊥-elim (true≢false (trans (sym eq)
    (root-above (switch α) (common δ (switch α)) (switch-on α n en))))
roots→WLPO D α | false = inj₂ (λ h → true≢false
  (trans (sym (root-keep (switch α) (common δ (switch α)) (switch-below α h))) eq))
  where
  open RootDispatch D

total-ψ→WLPO : ThreeEquations → S.WLPO
total-ψ→WLPO E = roots→WLPO (equations→roots E δ)
```

## 结论的范围与前提

主定理没有说所有总函数都不可能：`Fold` 显然有常零函数。它说在这个
未经限制的 `TΩ+1` raw 树扩张上，三个 BTBO 方程同时成立的总折叠蕴含 WLPO。
不带 `ThreeEquations` 的总函数、带证据的部分折叠、只在生成域上满足
方程的折叠、只要求序数值等价的方程，都不在陈述范围内。

三个条件律的触发域均非空：`switch (λ _ → false)` 触发保留行，
`j = δ` 触发同层行，`switch (λ _ → true)` 触发在上行。
下面给出编译器检查的见证；这不声称已经构造完整接口。

```agda
keep-premise : switch (λ _ → false) L.≺ᴵ δ
keep-premise = switch-below (λ _ → false) (λ _ → refl)

same-premise : δ L.≅ᴵ δ
same-premise = L.≅ᴵ-refl δ

above-premise : δ L.≺ᴵ switch (λ _ → true)
above-premise = switch-on (λ _ → true) 0 refl
```

完整接口的相容性另由 [TreeLevelsO7Model](TreeLevelsO7Model.lagda.md)
检查：所有 `Ordᴵ` 层号对的切口可判定时，`cuts→equations` 构造 `ThreeEquations`，
不需三歧、函数外延或证据唯一性。这是相对模型，切口判定本身不在此
无条件提供。不把三个触发域非空冒充完整接口已无条件居留。
这里的 `Common` 对任意层号对都可构造，因而此模型的 `Cuts` 不能读成
现有候选中已经解决的“合法同界内比较”。

**已编译定理。** `total-ψ→WLPO : ThreeEquations → Stage2.WLPO`。
证明实际只消费保留和在上两行，同层行作为完整三路契约保留。
这是对本篇明确写出的 raw 树扩张与字面方程的必要条件，不是“任何写法 A
都不可能”的量化定理，不据此否定乙线或其带合法性证据的现有候选。

**后续最小义务。** 若要把本篇推进到交接所要求的写法 A 结论，至少须：

1. 指出实际高层树及其合法性、内部 View，把 `lower j` 的共同作用域
   实现为该树上的字面第一位置，证明它与 `TΩ` 分支域的对应。
2. 给本篇所需的 raw 输入（至少上述开关节点）到实际树族的嵌入，
   连接低层分支域，并证明实际折叠导出这里的保留、同层、在上方程。
3. 若实际折叠只在合法域上定义，证明证明中所调用的开关输入及回灌输入
   在那个域内；`Common` 的现有构造不提供这项合法性。

这些桥目前没有定理。不能从本篇 raw 域上的结论推出任何候选已经失败，
也不能把这里的共同作用域证据计作已满足“律带合法公共上界”。

复现：仓库根目录，
`agda --library-file=<库文件> -i src -i probes probes/OCF/Align/TreeLevelsO7.lagda.md +RTS -M6G -RTS`，
退出码 **0**。模型文件用同一命令替换文件名，退出码 **0**。
两文件均是第 4 层文件，导入现有 `Stage2`（其闭包含记号），不进入成品。
没有新增候选闭项，没有新增无条件值下界，P1 的 x 仍是 Ω·ω²。
