# YiCarry V1：伴随证书与实际折叠域（共用接口，定稿）

本版把起点条件与 Reg 的全分支要求分开：Reg 仍覆盖原 Gd 的全部分支；
Carry 只沿带 LglB 的分支坐标递归。层参数 k 只带 Reg，不把它当作 ψ 的
源输入递归折叠；第一支仍带 Carry，以便沿原第一位置运输调用证据。
根为 lc 的 Carry 输入在第 0 层 ψ 中走 gt，故根下界带 Lgl。
这只指定允许调用的域，不声称实际 ψ 的链点已获得伴随证书。

V0 原样保留。指定保持与 tw 0..3、Ω̂ 2 的闭实例均已通过；
本篇与 YiCarryBounds 的定义、记录从此只增不改。
一般层读回按作者确认沿用 K1 环境，详见下文显式类型。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarry where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Cp; Lgl; Pre; Low; GdL)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiDispBase using (Below; one; more; e-suc; e-first)
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiCarryBounds public
  using (LglB; Nested; LglLow; cO-B; top-B; raw0-nested; add-B; ψᶜ-B; module ChainB)
import OCF.Align.YiK1 as K
import OCF.Align.RR4RegOmega2 as R
import OCF.Align.RR4CoordRoot as C
import OCF.Align.YiK2Base as A

Point : (k : LF) → Raw k → Set
Point k c = Σ (Raw k) (Gd k c)

Carry : LF → Set
Carry F.zero = ⊤
Carry (F.suc x) = Carry x
Carry (F.lim f) = ∀ n → Carry (f n)
Carry (F.lc k c t g) =
  Reg (F.lc k c t g) × Lgl k c × Carry t ×
  (∀ η e → LglB k η → Carry (g η e))

forget : ∀ {x} → Carry x → Reg x
forget {F.zero} r = tt
forget {F.suc x} r = forget {x} r
forget {F.lim f} r = λ n → forget {f n} (r n)
forget {F.lc k c t g} (reg , lc , ct , cg) = reg

lower : ∀ {k c t g} → Carry (F.lc k c t g) → Lgl k c
lower (reg , lc , ct , cg) = lc

start : ∀ {k c t g} → Carry (F.lc k c t g) → Point k c
start {k} {c} r = c , (inj₁ refl , lower r)

first-carry : ∀ {k c t g} → Carry (F.lc k c t g) → Carry t
first-carry (reg , lc , ct , cg) = ct

branch-carry : ∀ {k c t g} → Carry (F.lc k c t g) →
  ∀ η e → LglB k η → Carry (g η e)
branch-carry (reg , lc , ct , cg) = cg

cp-carry : ∀ {a b} → V.CP a b → Carry b → Carry a
cp-carry V.self r = r
cp-carry (V.suc p) r = cp-carry p r
cp-carry (V.lim n p) r = cp-carry p (r n)
cp-carry (V.fst p) r = cp-carry p (first-carry r)

read0-carry : ∀ (η : Raw F.zero) → Carry (V.up F.zero η)
read0-carry G.zero = tt
read0-carry (G.suc a) = read0-carry a
read0-carry (G.lim f) = λ n → read0-carry (f n)
read0-carry (G.lc () c t g)
read0-carry (G.em () t)
read0-carry G.top = tt

tw0-carry : Carry (V.tw 0)
tw0-carry = tt

tw1-carry : Carry (V.tw 1)
tw1-carry = tt

tw2-carry : Carry (V.tw 2)
tw2-carry = R.Ω₁-reg , tt , tt , (λ η e b → read0-carry η)
```

## 读回：沿用 K1 的块外环境

一般层的 top 读回是 Ω̂ k，LglB 只检查 Raw 的内部字段，不能独自给出
这个展开的 Reg。因此读回定理显式带 K1 的环境：Reg k、
Below k (Ω̂ k) 与 Carry (Ω̂ k)，输入仍须过原 cO 守卫。
Carry (Ω̂ k) 的 forget 正好给 K1 所需的 Reg (Ω̂ k)。

```agda
upN-carry : ∀ y (r : Pre y) (c : Low y r) t
  (g : (η : Low y r) → GdL y r c η → LF) →
  LglLow y r c → Reg (V.upN y r c t g) →
  Carry t → (∀ η e → Carry (g η e)) → Carry (V.upN y r c t g)
upN-carry F.zero () c t g lc reg ct cg
upN-carry (F.suc y) (inj₁ _) c t g lc reg ct cg =
  reg , lc , ct , (λ η e b → cg η e)
upN-carry (F.suc y) (inj₂ r) c t g lc reg ct cg =
  upN-carry y r c t g lc reg ct cg
upN-carry (F.lim f) (n , r) c t g lc reg ct cg =
  upN-carry (f n) r c t g lc reg ct cg
upN-carry (F.lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g lc reg ct cg =
  reg , lc , ct , (λ η e b → cg η e)
upN-carry (F.lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g lc reg ct cg =
  upN-carry k r c t g lc reg ct cg
upN-carry (F.lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g lc reg ct cg =
  upN-carry t₀ r c t g lc reg ct cg
upN-carry (F.lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g lc reg ct cg =
  upN-carry (g₀ η e) r c t g lc reg ct cg

top-read-carry : ∀ y → Reg y → Below y (V.Ω̂ y) → Carry (V.Ω̂ y) →
  ∀ (η : Raw y) → LglB y η → Cp y G.top η → Carry (V.up y η)
top-read-carry y ry root co G.zero b (inj₁ ())
top-read-carry y ry root co G.zero b (inj₂ ())
top-read-carry y ry root co (G.suc a) b (inj₁ ())
top-read-carry y ry root co (G.suc a) b (inj₂ p) =
  top-read-carry y ry root co a b p
top-read-carry y ry root co (G.lim f) ((st , lf) , bf) (inj₁ ())
top-read-carry y ry root co (G.lim f) ((st , lf) , bf) (inj₂ (n , p)) = term
  where
  term : ∀ m → Carry (V.up y (f m))
  term m with F.cmpC y (f (m + n))
    (subst (λ z → Cp y (f m) (f z)) (+-comm n m) (K.up-to y f st n m))
    (F.Cp-tr y p (K.up-to y f st m n)) (lf (m + n))
  ... | inj₁ below-top = cp-carry (V.cp→CP y below-top) co
  ... | inj₂ above-top = top-read-carry y ry root co (f m) (lf m , bf m) above-top
top-read-carry y ry root co (G.lc r c t g)
  ((tg , mono , irr , lt , lg) , lc , bc , bt , bg) (inj₁ ())
top-read-carry y ry root co (G.lc r c t g)
  ((tg , mono , irr , lt , lg) , lc , bc , bt , bg) (inj₂ p) =
  upN-carry y r c (V.up y t) (λ η e → V.up y (g η e)) lc
    (K.top-read-reg y ry root (forget co) (G.lc r c t g)
      (tg , mono , irr , lt , lg) (inj₂ p))
    (top-read-carry y ry root co t (lt , bt) p)
    (λ η e → top-read-carry y ry root co (g η e) (lg η e , bg η e)
      (F.Cp-tr y p (tg η e)))
top-read-carry y ry root co (G.em i a) b (inj₁ ())
top-read-carry y ry root co (G.em i a) b (inj₂ ())
top-read-carry y ry root co G.top b p = co

guard-read-carry : ∀ y → Reg y → Below y (V.Ω̂ y) → Carry (V.Ω̂ y) →
  ∀ η → Gd y (V.cO y) η → LglB y η → Carry (V.up y η)
guard-read-carry F.zero ry root co η e b = read0-carry η
guard-read-carry (F.suc y) ry root co η e b =
  top-read-carry (F.suc y) ry root co η b (proj₁ e)
guard-read-carry (F.lim f) ry root co η e b =
  top-read-carry (F.lim f) ry root co η b (proj₁ e)
guard-read-carry (F.lc k c t g) ry root co η e b =
  top-read-carry (F.lc k c t g) ry root co η b (proj₁ e)
```

## 指定规范实例

Ω̂ 2 的 Reg 仍使用原全部分支定理；只有额外的 Carry 分支要求使用 LglB。
tw 3 的第 0 层坐标递归沿 K1 的公共界进行，后继行用刚证得的读回保持。
下面只填指定闭实例，不给全塔或 Λ 的证书。

```agda
Ω₂-carry : Carry (V.Ω̂ (F.suc (F.suc F.zero)))
Ω₂-carry = R.Ω₂-reg , tt , tw2-carry ,
  (λ η e b → guard-read-carry (F.suc F.zero) tt (one e-first) tw2-carry η e b)

under-one-omega-carry : ∀ (a : Raw F.zero) → Cp F.zero a R.raw1 →
  Carry (V.Ω̂ (V.up F.zero a))
under-one-omega-carry a (inj₁ refl) = tw2-carry
under-one-omega-carry a (inj₂ (inj₁ refl)) = tt
under-one-omega-carry a (inj₂ (inj₂ ()))

coordinate-omega-carry : ∀ (η : Raw F.zero) → Lgl F.zero η →
  Cp F.zero R.raw1 η → Carry (V.Ω̂ (V.up F.zero η))
coordinate-omega-carry G.zero l (inj₁ ())
coordinate-omega-carry G.zero l (inj₂ ())
coordinate-omega-carry (G.suc a) l (inj₁ refl) = tw2-carry
coordinate-omega-carry (G.suc a) l (inj₂ p) =
  K.coordinate-omega-reg (G.suc a) l (inj₂ p) ,
  proj₁ (cO-B (V.up F.zero a)) ,
  coordinate-omega-carry a l p ,
  (λ ζ d b → guard-read-carry (V.up F.zero a) (R.read0-reg a)
    (C.coordinate-root (a , (p , l))) (coordinate-omega-carry a l p) ζ d b)
coordinate-omega-carry (G.lim f) (st , lf) (inj₁ ())
coordinate-omega-carry (G.lim f) (st , lf) (inj₂ (n , p)) = term
  where
  term : ∀ m → Carry (V.Ω̂ (V.up F.zero (f m)))
  term m with F.cmpC F.zero (f (m + n))
    (subst (λ z → Cp F.zero (f m) (f z)) (+-comm n m)
      (K.up-to F.zero f st n m))
    (F.Cp-tr F.zero p (K.up-to F.zero f st m n)) (lf (m + n))
  ... | inj₁ below-one = under-one-omega-carry (f m) below-one
  ... | inj₂ above-one = coordinate-omega-carry (f m) (lf m) above-one
coordinate-omega-carry (G.lc () c t g) l p
coordinate-omega-carry (G.em () t) l p
coordinate-omega-carry G.top l (inj₁ ())
coordinate-omega-carry G.top l (inj₂ ())

tw3-carry : Carry (V.tw 3)
tw3-carry = K.tw3-reg , tt , tw2-carry ,
  (λ η e b → coordinate-omega-carry η (proj₂ e) (proj₁ e))
```

## 下游目标记录：只陈述，不填实现

K1′ 交全塔与极限的 Carry，不把已有四个闭实例冒称全塔。
K2′ 的输入是同一 LF 上并列的 Carry 与 Legal，输出为原 Raw 0，
同时交 LglB、读回后的 Legal、正输出以及带公共界的位置保持。

```agda
record K1′ : Set where
  field
    tower : ∀ n → Carry (V.tw n)
    limit : Carry V.Λ

record Source : Set where
  constructor source
  field
    term : LF
    carried : Carry term
    lawful : V.Legal term
open Source public

branch-legal : ∀ {k c t g} → V.Legal (F.lc k c t g) →
  ∀ η e → V.Legal (g η e)
branch-legal (lk , first , mono , irr , lt , lg) = lg

branch-source : ∀ {k c t g} (r : Carry (F.lc k c t g)) →
  V.Legal (F.lc k c t g) → ∀ η e → LglB k η → Source
branch-source {g = g} r l η e b =
  source (g η e) (branch-carry r η e b) (branch-legal l η e)

record Common (a b : LF) : Set where
  constructor common
  field
    upper : LF
    upper-legal : V.Legal upper
    left : V.CP a upper
    right : V.CP b upper

-- 有向 Raw 律的字面公共界固定为右项 b，并显式保存该界合法性。
record RawStep (k : LF) (a b : Raw k) : Set where
  field
    path : Cp k a b
    target-legal : Lgl k b

record PointB (k : LF) (c : Raw k) : Set where
  constructor point
  field
    coordinate : Raw k
    guard : Gd k c coordinate
    bounds : LglB k coordinate
open PointB public

-- 第 0 层可把原 start 升成 PointB；更高层的生成器要自己交 seed。
start0-B : ∀ {c t g} → Carry (F.lc F.zero c t g) → PointB F.zero c
start0-B {c} r = point c (inj₁ refl , lower r) (lower r , raw0-nested c)

record GtGenerator (ψ : Source → Raw F.zero)
  (k : LF) (c : Raw k) (t : LF)
  (g : (η : Raw k) → Gd k c η → LF)
  (r : Carry (F.lc k c t g)) (l : V.Legal (F.lc k c t g)) : Set where
  field
    seed : PointB k c
    next : PointB k c → PointB k c
    grow : ∀ p → F.Dn k (coordinate p) (coordinate (next p))
    output-step : ∀ p →
      RawStep F.zero
        (ψ (branch-source r l (coordinate p) (guard p) (bounds p)))
        (ψ (branch-source r l (coordinate (next p))
          (guard (next p)) (bounds (next p))))

iterate : ∀ {X : Set} → (X → X) → X → ℕ → X
iterate step initial zero = initial
iterate step initial (suc n) = step (iterate step initial n)

generated : ∀ {ψ k c t g r l} → GtGenerator ψ k c t g r l → ℕ → PointB k c
generated d = iterate (GtGenerator.next d) (GtGenerator.seed d)

generated-out : ∀ (ψ : Source → Raw F.zero) k c t g r l →
  GtGenerator ψ k c t g r l → ℕ → Raw F.zero
generated-out ψ k c t g r l d n =
  ψ (branch-source r l (coordinate p) (guard p) (bounds p))
  where
  p : PointB k c
  p = generated d n

record PsiRows (ψ : Source → Raw F.zero) : Set where
  field
    gt-generator : ∀ k c t g r l → GtGenerator ψ k c t g r l
    zero-row : ∀ r l → ψ (source F.zero r l) ≡ A.one
    suc-row : ∀ x (r : Carry x) (l : V.Legal x) →
      ψ (source (F.suc x) r l) ≡ A.successor (ψ (source x r l))
    lim-row : ∀ f (r : ∀ n → Carry (f n))
      (st : ∀ n → V.CP (f n) (f (suc n))) (l : ∀ n → V.Legal (f n)) →
      ψ (source (F.lim f) r (st , l)) ≡
      G.lim (λ n → ψ (source (f n) (r n) (l n)))
    gt-row : ∀ k c t g r l →
      ψ (source (F.lc k c t g) r l) ≡
      G.lim (generated-out ψ k c t g r l (gt-generator k c t g r l))
    gt-additive0 : ∀ c t g r l (p : PointB F.zero c) →
      coordinate (GtGenerator.next (gt-generator F.zero c t g r l) p) ≡
      A._+ʳ_ (coordinate p)
        (ψ (branch-source r l (coordinate p) (guard p) (bounds p)))
    gt-seed0 : ∀ c t g r l →
      coordinate (GtGenerator.seed (gt-generator F.zero c t g r l)) ≡ c

OutputB : (Source → Raw F.zero) → Set
OutputB ψ = ∀ s → LglB F.zero (ψ s)

record K2′ : Set where
  field
    ψ : Source → Raw F.zero
    rows : PsiRows ψ
    output-B : OutputB ψ
    output-legal : ∀ s → V.Legal (V.up F.zero (ψ s))
    positive : ∀ s → F.Dn F.zero G.zero (ψ s)
    bounded-position : ∀ a b → Common (term a) (term b) →
      V.CP (term a) (term b) → RawStep F.zero (ψ a) (ψ b)
```

四行各自的交付字段如下；每个字段都是构造方要证的目标，未作模块假设
来冒称已有完整折叠。PsiRows／K2′ 目前没有整记录的实例。

| 行 | 输入与生成需要的证据 | 输出需要的证据 |
|---|---|---|
| 零 | Source 的 Carry、Legal；取字面 one | 原合法性、LglB、从 0 出发的 Dn |
| 后继 | 前驱 Source；复制从 0 起，用输出正性与右递归加法生成步进 | copies 的 Cp／Lgl，新增条件由 Raw 0 的 raw0-nested 给出 |
| ℕ 极限 | 每支 Source，原相邻 CP；两项的公共界就是合法后一项 | 逐支 LglB 与带界位置保持给原极限合法性 |
| gt | 根 start；分支调用必须同时有原 guard 与 LglB。GtGenerator 要实际构造 seed、next，next 的返回类型包含下一点的 guard 与 LglB，另交 grow／output-step | 链上每支由 output-B 给 LglB；相邻 output-step 与合法后一支给原极限合法性 |

第 0 层坐标链另由 gt-additive0、gt-seed0 固定为 K2 的加法更新及下界起点。
它的新增证据生产使用 start0-B、add-B 与 ψ 输出的 output-B；
这不是给一条未解释的点列再假定全部链点都好。
GtGenerator 的 grow 是实现必须交付的证明，完整 K2′ 目前未填；
已有 YiK2Base.Chain 的 grow 则已经由规则生成。
高层 k 的 next 生成式尚未在本轮实现，需由下游交生成器及其上述证据。

Carry 根只有 Lgl c，不凭空推断高层 LglB c：GtGenerator 的高层 seed
仍是明确目标。第 0 层 start0-B 利用该层无嵌套 lc 的事实，已编译给出。
这一区分保留给构造与否定共用，不能用规范 cO 有证据冒称任意下界也有。

## 否定路的目标类型

下面只定义待攻的类型，没有构造反例或证明这些类型为空。
第 0 层的嵌套条件自动成立，所以 OutputB 在本接口上还要求原输出 Lgl；
若已有输出 Lgl，不能单凭“有嵌套坏下界”在 Raw 0 攻破它。

```agda
record ReadOmegaCounterexample : Set where
  field
    index : LF
    index-reg : Reg index
    index-root : Below index (V.Ω̂ index)
    omega-carry : Carry (V.Ω̂ index)
    input : Raw index
    input-guard : Gd index (V.cO index) input
    input-B : LglB index input
    fails : Carry (V.Ω̂ (V.up index input)) → ⊥

record OutputBCounterexample (ψ : Source → Raw F.zero) : Set where
  field
    input : Source
    fails : LglB F.zero (ψ input) → ⊥
```

读回环境的正面前提有实例：index=0 时取 tt、one e-suc、tt，
输入取 raw1，守卫自反、LglB 为 tt 与 tt；这里只说明前提非空，
没有给 fails。Source 的五个规范实例由本篇闭证据与原 Legal-tw／Legal-Ω₂
并列给出；同样不将未填的 PsiRows 或 K2′ 冒称可满足的条件定理。

## 律的字面公共上界检查

| 出现的一对／律 | 字面公共界及证据 | 检查结果 |
|---|---|---|
| LglB 的原 Lgl 部分 | 原极限相邻项以后一项为界；原 lc 单调性以 GdL 给出的后一坐标为界 | 只增加嵌套证书，不扩张原律的定义域 |
| 起点中的 c、c | c；自反 Cp，根 lower 给 Lgl c | 不判等或比较裸下标 |
| top-read-carry 的 top、f m | 同一项 f(m+n)；K.up-to 给 f m 到该项的 Cp，已知 top 的路径接到该项，lf(m+n) 给合法性 | 与 K1 相同的有界比较 |
| coordinate-omega-carry 的 raw1、f m | 同一项 f(m+n)，两条 Cp 与该项 Lgl 在调用 cmpC 前明确给出 | 与 K1 相同的有界比较 |
| cp-carry 的 a、b | 已给 CP a b，字面祖先 b | 只沿后继、极限及第一支投影证据，不运行比较器；不把缺少 Legal 的路径送入比较器 |
| Reg 的 suc k、结点 | 原 Below 路径提供结构祖先 | Below 可以过 Ω 支，仍不作为第一位置比较器的 CP 公共界 |
| K2′ 的 bounded-position 源项对 | Common 显式保存 upper、两条 CP 与 Legal upper | 不对两个独立 Source 提供无界比较律 |
| GtGenerator 的相邻坐标 | next p 的 coordinate；grow 给 Dn，转为 Cp，另有自反；next p 的 bounds 给合法性 | next 返回带原 guard 与 LglB 的完整点包 |
| GtGenerator 的相邻源分支 | 后一分支；原 Legal 的 mono 用 grow 转成的 Gd 给前一到后一的 CP；branch-legal 给后一合法性 | 只用于已经生成的相邻点 |
| output-step、bounded-position 的 Raw 输出对 | 右输出；RawStep.path 和自反给两条 Cp，RawStep.target-legal 显式给界合法性 | 独立使用这些记录时也不丢公共界合法性 |
| 原 ChainB 的 next／chain | 原 Chain 已构造的下一点与其 Gd，伴随 LglB 经 add-B／ψᶜ-B 生成 | 没有新增坐标比较或 Grow 假设 |
| 四行等式与 gt-additive0／gt-seed0 | 规定同类型上的执行等式 | 不提供判等器或全局三歧，不比较两个裸下标的序 |

第 0 层 ψ 的 lc 行比较 suc k 与 0 时，可取合法的 suc k 为公共界：
自身的 CP 自反和 0 到它的第一位置都存在，Legal k 由源 Legal 给出。
本篇没有构造这项判定或完整 ψ。非零目标辅助层若另有比较，
下游仍必须逐对交公共界，不能从 PointB 或 Reg 推出全局可比性。

## 条件定理与 K1′ 的每步义务（作者补充）

guard-read-carry 是**条件编译定理**：它的三个环境前提 Reg k、
Below k (Ω̂ k)、Carry (Ω̂ k) 与输入的原 cO 守卫、LglB 均显式保留。
不是 LglB 单独推出读回 Carry，也没有把环境作为公理。
前提逐个可满足的两组闭实例在 YiCarryExamples：

- k=0：zero-env-reg、zero-env-root、zero-env-carry、zero-input-guard、
  zero-input-B，并由 zero-conditional-read 实际应用该条件定理。
- k=V.tw 2（Ω₁）：omega1-env-reg、omega1-env-root、omega1-env-carry、
  omega1-input-guard、omega1-input-B，由 omega1-conditional-read 实际应用。
  其中 omega1-env-carry 使用本篇 tw3-carry，后者的 Reg 来自 K1.tw3-reg。

**Carry (Ω̂ k) 正是 K1′ 全塔归纳每一步要交的义务，本轮不证一般 k。**
用该前提给读回保持，不等于从 Carry k 自动生产下一项；
本篇闭实例的构造已经分别实填了所用环境，没有用待证的全塔记录。
指定五项均已实填，条件定理没有掩盖任何规范实例的前提缺口。

## 翻译账、定稿范围与止损核对

LglB 的下界字段由原 Gd 的启动要求及 V0 编译反例逼出；
新字段不取自记号基本列。它递归检查 Raw 的全部原分支，
而 Carry 的递归分支只在 LglB 坐标上开放；原树与原 Gd 不改。
Reg 仍直接按旧定义取原全部守卫分支，不用伴随证书缩减其量词。
Carry 的第一支递归服务于 CP 运输，不将层参数 k 当作折叠源。

规范实例的两次 Ω 递归沿用 K1 的树侧公共界和已有 Reg 证明，
新增起点只读原 cO 的合法性，新增分支条件只读 LglB。
零／复制／逐点极限／gt 链输出四行仍参考 K2 的原模板；
它们现在只是下游目标记录，没有写出完整折叠或从树侧唯一性定理。
第 4 层逼出：无。没有强度或 FGH 比较，不称树自足已经完成。

止损核对：cO、Raw 0 加法、ψᶜ、原 Chain 的伴随证书保持，
带作者确认环境的 up 读回保持，以及五个指定规范闭实例均已编译通过。
V0 坏坐标不能带 LglB 的否定只在 YiCarryExamples 核对，
未触发 V1 的规范实例止损。主接口不导入 V0 或该核对叶模块。
K1′／K2′、ReadOmegaCounterexample 与 OutputBCounterexample 均只有类型，
没有整记录实现或否定；更高生成保持仍交下游构造与否定共用。

## 冷编与引用审计（2026-11-10）

| 本轮模块 | 删除自身接口后重编 | 单路堆上限 | 退出码 | 目标 Checking |
|---|---|---|---|---|
| YiCarryBounds | 是 | 6G | 0 | 有 |
| YiCarry | 是 | 6G | 0 | 有 |
| YiCarryExamples | 是 | 6G | 0 | 有 |

依赖用缓存，不声称冷编整个闭包。所有 Agda 顺序执行，退出码直接读取，
没有通过管道。每次均带 `+RTS -M6G -RTS`；仅删除本轮三个模块自己的接口。
V0 的字节摘要与开工时相同，未改源文件或删除其接口。

复现（从仓库根，库文件包含 stdlib 与 cubical 的库路径）：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryBounds.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarry.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryExamples.lagda.md +RTS -M6G -RTS
python3 probes/Survey/scripts/importclosure.py OCF.Align.YiCarryBounds OCF.Align.YiCarry OCF.Align.YiCarryExamples --only OCF.Align.Yi --only OCF.Align.RR4RegOmega2 --only OCF.Align.RR4CoordRoot --only OCF.Align.LevelFix --only OCF.Free.Level --only OCF.BTBO
```

- 三件均 `--safe --without-K --lossy-unification`；公设、洞、跳过停机／
  正性检查的指示、信任相等及 Funext 前提均为 0；无绝对路径、临时日志路径、
  尾随空白。没有安装包、提交、推送或改旧数学定义。
- Bounds／主接口／Examples 的源码本地闭包分别 6／22／25，库叶 13／19／19，
  白名单外及禁用表均为 0，无记号或 C 线。三份成功编译器图的本地集合
  与源码逐一相同；主接口不导入 V0／Examples。
- 成功 HTML 的切片：LglB 25、cO-B 30、add-B 33、ψᶜ-B 43、chain-B 56、
  Carry 32、guard-read-carry 81、tw3-carry 109、Ω₂-carry 96、
  no-v0-bad-coordinate-B 36 个块；各根记号模块／记号词命中均为 0。
  正对照 EboLean3Lab 的 ebo-lab″ 为 352／33／36，不在主接口闭包。
  切片为语法近似，不能代替条件前提核对或序数值验收。
- k=0 与 k=Ω₁ 的条件前提逐项闭实例和读回应用另在 Examples 编译，
  不以空前提替代定理。规范五项均通过；完整全塔、ψ 与否定目标均未证。

本轮编译定理、条件编译定理及未证目标如上分列；有限测试无。
README 与 LOG 只新增本轮状态和翻译账，不改 V0 或旧结论。
