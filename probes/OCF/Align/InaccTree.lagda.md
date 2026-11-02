# 不可达层的树侧 (层 1–2): 裸层号宇宙、外部派发, 以及它对现行 EBO 工作的启示

> 底座 [InaccTreeBase](InaccTreeBase.lagda.md), 与记号的比较只在 [InaccTreeAccept](InaccTreeAccept.lagda.md). 结论先说:
>
> 1. **层 1–2 成立, 代价是一个外部判决.** 层号是裸的归纳-递归宇宙 `Lv` (`limᴼ k g` 不带证据, `toLv` 总函数), 树族 `Ordᴸ` 与 Level 的 `Ord₊` 同形: `limᴼ` 的共尾节点就是 "参数层 `k` 上的 `limᵢ`", 不需要新构造子. 折叠 `Fold.ψ` 对**任何**判决 `D : Lv → Lv → Verdict` 都是总函数, 与 Level 的 ψ 逐子句相同, 只把 `<ᴵ-dec` 换成 `D`; 它只有 12 行. 所有闭项 (ψ₀(Ω_Ω·2)、(Ω_Ω)²、ψ₀(Ω_{Ω+1})、ψ₀(Ω_{Ω_Ω})、**EBO = ψ₀(Λ)**、ψ₀(I)、ψ₀(Ω_{I+1})、ψ₀(Ω_{I+2})) 对任意 `D` 都有定义. **但它们的值只在 `D` 对访问点答对时才是所称的序数; 除有限层外没有任何一个判决被证实**, 所以 "定义了 EBO" 的意思只是层 2 的 "合法性由外部给定", 而外部这份东西目前是启发式 `ver` (脚手架, `ver-wrong` 证明它在采样外是错的).
> 2. **中心问题的回答: 比较两个前驱 `g x`, `g y` 不是问题, ℕ-极限才是.** 有向性 `Dir` 在裸树上是定理 (`dir-L₁`, 公共上界 `lim [x,y,y,…]`). 败的是它下面的步进: `¬WF-L₁` (`WF` 证书对 Ω_Ω 层号无居留), `noBT` (以 Ω_Ω 为界的结构三歧直接是假的, 不只是推出 WLPO; scout 的 `Trich₂→WLPO` 低估了), `¬SoundAll` (对穿透分支的全部输入量化的正确性是假的). 所以判决不能来自 "`c` 是好界" 这样的单一证书. `<-dec`/`tr`/`res`/`≅` 都已写好 (InaccTreeBase §4–§5), 对 `WF` 界成立, 且 `≅` 是普通数据类型 (`limᴼ` 带显式互搬 `u`, `v`), 不必进 IR 块; 但 `WF` 够不到 Ω_Ω.
> 3. **替身与前缀塔从定义里消失, 逐项与 EBO 一致 (验收, `ver` 下).** ψ_Ω(Y) 就是目标为 `L₁` 的普通折叠, 现行的帧 `Ψ` 是它的 CPS 形式, 深度 `d` 是嵌套次数, 无地板、无 `Mlev`、无 `ŝ`/`ĉᴸ`、无 `force`; 目标不低于树层时连判决都不用 (`ψ↓`, 9 行). 在 `low-term`、`low-pop`、OmegaSqA §5 的路径 θ₁ `[0,1,0,0,0,2,0]` 上都与 EBO 一致 (`low-ok`, `low-pop-ok`, `θ-ok`). **极限层下降:** 新折叠没有地板, `up n` 定义性透明 (`up-lim`), 所以现行 `fold` 的 `fk L₁` 偏差与它的 `fb K` 修正都不发生. `¬AlignΩ₃`、`¬BranchΩ`、`¬BranchΩᴬ` 的反例作为定义问题消失 (`up-transparent`, 对一切判决 refl); 它们的**内容**转移到判决: 现在每个比较要有证据, 证据的来源未解决.
> 4. **难度搬到了判决, 没有消失.** `verN` (只答有限数) 在 `tΩ2` 上第一次出错的路径是 `[2,2,2,0,0,0,0]` (`first-nonnat`), 两边都是链点派生的 ℕ-极限层号, 正是 `Growth`/`dd₀` 管的事. 证书类型 `Cert.Run` 比 `Goodᴸ` 小 (6 个构造子, 无地板), 但好输入 `G` 是参数, 单调证据删不掉 (`not-step`), 所以它的内容与 `Goodᴺ`/`Occ≺ᴳ` 的非地板部分同一.
> 5. **降维打击: 既未成功也未被否定.** 单一命题是 `Strike P`, 拆成 `Agree`/`OrderEmb` 与基本列交换. 编译的部件: 一个翻译 `⟦_⟧` 覆盖全部 EBO 文法, 规则 0/和/4/5/6 的形状 refl (`Pieces`). 编译的否定只杀掉 "单一 `WF` 界" 这一种证书形式. 第一个具体障碍: 判决只看到层号, 看不到记号; 只看层号而对全部 NF 下标正确的总函数, 仓库里没有构造, 也没有否定; 走记号一侧则 `OrderEmb` 就是全 EBO 上的 Bachmann 性质, 而全 EBO 的 NF 谓词尚不存在 (`NF₁` 只到一个不可数下标). (勘误 2026-11-02: 全 EBO 的标准形谓词现在有了, 见 [EBOI](EBOI.lagda.md) 的 `isOTᵉ`; 降维打击的裁决见 [InaccStrike](InaccStrike.lagda.md): `ver` 的树确实偏离 EBO, 结论是 PLATFORM.)
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 本文与底座的导入链不含 `OCF.Align.EBO`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst) renaming (trans to trans′)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase
```

## §1 Ω-封闭的层号与编译的否定

`L₁` 是 Ω_Ω 作为层号: 第 0 层全部树的层号的上确界. `toLv (Ω 1)` 字面就是它.

```agda
L₁ : Lv
L₁ = limᴼ zero toLv

_ : toLv (Ω {- 1 -} (suc zero)) ≡ L₁
_ = refl

natT : ∀ {k} → ℕ → Ordᴸ k
natT zero    = zero
natT (suc n) = suc (natT n)

natL : ℕ → Lv
natL zero    = zero
natL (suc n) = suc (natL n)
```

**否定 1: 有向性是免费的.** scout 以为 `limᴼ` 的中心问题是分支族有向性 `Dir`. 在裸树上它是定理: 任意两棵树的公共上界就是 `lim [x, y, y, …]`.

```agda
joinT : Ordᴸ zero → Ordᴸ zero → Ordᴸ zero
joinT x y = lim (λ { zero → x ; (suc _) → y })

dir-L₁ : ∀ x y → Σ (Ordᴸ zero) λ z → toLv x ⊑ toLv z × toLv y ⊑ toLv z
dir-L₁ x y = joinT x y , (λ r → via (0 , r) (≅-refl _)) , (λ r → via (1 , r) (≅-refl _))
```

**否定 2: 障碍全在 `limᴼ` 之下的 ℕ-极限.** 代价是公共上界 `joinT` 不步进. `WF L₁` 恰好败在 "每个分支 WF": 分支 `lim [1, 0, 0, …]` 不步进.

```agda
zigzag : Ordᴸ zero
zigzag = lim (λ { zero → suc zero ; (suc _) → zero })

¬WF-L₁ : WF L₁ → ⊥
¬WF-L₁ (_ , _ , w) with proj₁ (w zigzag) 0 (inj₁ tt)
... | via () _
```

**否定 3: 以 `L₁` 为界的结构三歧直接是假的 (不只是推出 WLPO).** `≅` 是结构的, `lim [1,2,3,…]` 与 `ω+1` 既不 `≺` 也不 `≅`. 所以 scout 的 `Trich₂→WLPO` 还低估了: 在结构序下无界三歧连经典地都不成立; 值序下的版本才是壁垒定理的 LPO.

```agda
data IsNat : Lv → Set where
  nz : IsNat zero
  ns : ∀ {a} → IsNat a → IsNat (suc a)

natIs : ∀ n → IsNat (natL n)
natIs zero    = nz
natIs (suc n) = ns (natIs n)

atNat : ∀ {a} → IsNat a → (r : Pre a) → IsNat (at a r)
atNat (ns i) (inj₁ _) = i
atNat (ns i) (inj₂ r) = atNat i r

lim≇nat : ∀ {f b} → IsNat b → ¬ (lim f ≅ b)
lim≇nat nz ()
lim≇nat (ns _) ()

nat-neq : ∀ n → ¬ (natL (suc n) ≅ natL n)
nat-neq zero    ()
nat-neq (suc n) (s≅ e) = nat-neq n e

BT : Lv → Set
BT c = (p q : Pre c) → Trichʹ (at c p) (at c q)

ωT ω⁺T : Ordᴸ zero
ωT  = lim natT
ω⁺T = lim (λ n → natT (suc n))

toLv-nat : ∀ n → toLv {zero} (natT n) ≡ natL n
toLv-nat zero    = refl
toLv-nat (suc n) rewrite toLv-nat n = refl

noBT : BT L₁ → ⊥
noBT bt with bt (inj₂ (suc ω⁺T , inj₁ tt)) (inj₂ (suc (suc ωT) , inj₁ tt))
... | injᵃ (via (inj₁ _) (l≅ h)) = nat-neq 0 (h 0)
... | injᵃ (via (inj₂ (m , s)) e) = lim≇nat (atNat (natIs′ m) s) e where
  natIs′ : ∀ m → IsNat (toLv {zero} (natT m))
  natIs′ m = subst IsNat (sym (toLv-nat m)) (natIs m)
... | injᵇ (via (n , s) e) = suc≇nat (atNat (natIs′ n) s) e where
  suc≇nat : ∀ {f b} → IsNat b → ¬ (suc (lim f) ≅ b)
  suc≇nat nz ()
  suc≇nat (ns i) (s≅ e′) = lim≇nat i e′
  natIs′ : ∀ m → IsNat (toLv {zero} (natT (suc m)))
  natIs′ m = subst IsNat (sym (toLv-nat (suc m))) (natIs (suc m))
... | injᶜ ()
```

## §2 闭项 (层 2): 任何判决下都是总函数

下面的闭项对启发式判决 `ver` (InaccTreeBase §6) 实例化. **所有项对任意 `Oracle` 都有定义**; `ver` 只决定它们的值是否对. 哪些项的判决可被证实, 见 §5.

```agda
module Terms (D : Oracle) where
  open Fold D public

  ψ⁰ : ∀ {k} → Ordᴸ k → Ordᴸ zero
  ψ⁰ = ψ {zero}

  Ω̂ : Ordᴸ L₁
  Ω̂ = Ω L₁

  ψ_Ω : ∀ {k} → Ordᴸ k → Ordᴸ L₁
  ψ_Ω = ψ {L₁}

  ΩL : Lv → Lv
  ΩL ℓ = toLv (Ω ℓ)

  Λ : Lv
  Λ = lim (iter ΩL zero)

  T₁ T₂ TΩΩ TO+1 TΩ2Ω TΩΩΩ EBOᵀ : Ordᴸ zero
  T₁    = ψ⁰ Ω̂                    -- ψ₀(Ω_Ω)
  T₂    = ψ⁰ (Ω̂ + Ω̂)              -- ψ₀(Ω_Ω·2)
  TΩΩ   = ψ⁰ (ψ_Ω Ω̂)              -- ψ₀(Ω_Ω·Ω_Ω) = ψ₀((Ω_Ω)²)
  TO+1  = ψ⁰ (Ω (suc L₁))         -- ψ₀(Ω_{Ω+1})
  TΩ2Ω  = ψ⁰ (Ω (toLv (Ω̂ + Ω̂)))   -- ψ₀(Ω_{Ω·2})
  TΩΩΩ  = ψ⁰ (Ω (ΩL L₁))          -- ψ₀(Ω_{Ω_Ω})
  EBOᵀ  = ψ⁰ (Ω Λ)                -- ψ₀(Λ) = EBO

  -- ψ_Ω 不需要判决: 目标就是树的层
  ψ_Ω↓ : Ordᴸ L₁ → Ordᴸ L₁
  ψ_Ω↓ = ψ↓ (σ-id L₁)

  TΩΩ↓ : Ordᴸ zero
  TΩΩ↓ = ψ⁰ (ψ_Ω↓ Ω̂)

  _ : ΩL zero ≡ suc zero
  _ = refl
  _ : ΩL (suc zero) ≡ L₁
  _ = refl
  _ : ΩL L₁ ≡ limᴼ zero (λ x → ΩL (toLv x))
  _ = refl
  _ : iter ΩL zero 3 ≡ ΩL L₁
  _ = refl

  -- ψ₀(Ω_Ω) 的链: 目标 0 永远 rise 当且仅当判决这么说; 形状对一切 D 由 D 0 0 决定
  Ω̂at : (x : Ordᴸ zero) → Ordᴸ L₁
  Ω̂at x = up x (Ω (toLv x))

  chainΩ̂ : (D zero zero ≡ rise) → T₁ ≡ lim (λ n → ψ⁰ (Ω̂at (iter (λ x → ψ⁰ (Ω̂at x)) (suc zero) n)))
  chainΩ̂ e with D zero zero | e
  ... | rise | refl = refl
```

**折叠对 `up` 透明 (定义性).** 这是 `¬AlignΩ₃` 与 `¬BranchΩ` 的反例在此处消失的原因: 反例的两个输入 `suc zero` 与 `up zero (up zero 1)` 只在类型地板上不同; 这里没有地板, 两者的折叠字面相等, 对一切判决、一切目标.

```agda
module Transparent (D : Oracle) where
  open Fold D

  x₃ y₃ : Ordᴸ (natL 2)
  x₃ = suc zero
  y₃ = up tt (up tt (suc zero))

  up-transparent : ∀ {i} → ψ {i} x₃ ≡ ψ {i} y₃
  up-transparent = refl

  -- 同样, 把任一层的树提上任一层, 折叠不变
  up-any : ∀ {i k} (x : Ordᴸ k) → ψ {i} {suc k} (up tt x) ≡ ψ {i} x
  up-any x = refl

  -- 极限层下降: 没有地板要保留或收紧, `up n` 对一切目标透明
  up-lim : ∀ {i f} n (x : Ordᴸ (f n)) → ψ {i} {lim f} (up n x) ≡ ψ {i} x
  up-lim n x = refl

  -- limᴼ 层同样
  up-limᴼ : ∀ {i k g} (y : Ordᴸ k) (x : Ordᴸ (g y)) → ψ {i} {limᴼ k g} (up y x) ≡ ψ {i} x
  up-limᴼ y x = refl
```

## §3 I 层: 树、ψ_I 与 ψ_i

`OrdI B` 是 I+k 层的树, `B` 是下一梯级的树类型. 每个 `ℓ : Lv` 都是前驱 (`limᵢ`, `up`), `limᴵ` 是 I-共尾节点, `limB`/`upB` 是下一梯级的分支与嵌入. `OrdI ⊥` 是 I 层本身.

```agda
data OrdI (B : Set) : Set where
  zero : OrdI B
  suc  : OrdI B → OrdI B
  lim  : (ℕ → OrdI B) → OrdI B
  limᵢ : (ℓ : Lv) → (Ordᴸ ℓ → OrdI B) → OrdI B
  limᴵ : (Lv → OrdI B) → OrdI B
  limB : (B → OrdI B) → OrdI B
  up   : (ℓ : Lv) → Ordᴸ ℓ → OrdI B
  upB  : B → OrdI B

Ωᴵ : ∀ {B} → OrdI B
Ωᴵ = limᴵ (λ ℓ → up ℓ (Ω ℓ))

Ωᴵ⁺ : ∀ {B} → OrdI B
Ωᴵ⁺ = limB upB

reseed : ∀ {B} → Lv → OrdI B
reseed L = up L (Ω L)

module ITier (D : Oracle) where
  open Terms D

  nextFix : Lv → Lv
  nextFix L = lim (iter ΩL (suc L))

  -- ψ_I: 目标是 I 自身, 从不派发; 输出是层号
  ψᴸ  : ∀ {k} → Ordᴸ k → Lv
  ψᴸ zero    = Λ
  ψᴸ (suc a) = nextFix (ψᴸ a)
  ψᴸ (lim f) = lim (λ n → ψᴸ (f n))
  ψᴸ {k} (limᵢ r f) = limᴼ (at k r) (λ y → ψᴸ (f (intoL k r y)))
  ψᴸ {suc k}    (up d x) = ψᴸ x
  ψᴸ {lim f}    (up d x) = ψᴸ x
  ψᴸ {limᴼ k g} (up d x) = ψᴸ x

  -- B 处的链目标 I: fromLv 把层号回灌成 B 的元素 (I+1 层时 fromLv = reseed)
  module Tier {B : Set} (ΩB : B) (fromLv : Lv → B) (ψIB : B → Lv) (ψLB : ∀ {i} → B → Ordᴸ i) where
    ψI : OrdI B → Lv
    ψI zero       = Λ
    ψI (suc a)    = nextFix (ψI a)
    ψI (lim f)    = lim (λ n → ψI (f n))
    ψI (limᵢ ℓ f) = limᴼ ℓ (λ y → ψI (f y))
    ψI (limᴵ f)   = lim (λ n → ψI (f (iter (λ L → ψI (f L)) Λ n)))
    ψI (limB f)   = lim (λ n → ψI (f (iter (λ x → fromLv (ψI (f x))) ΩB n)))
    ψI (up ℓ x)   = ψᴸ x
    ψI (upB b)    = ψIB b

    ψL : ∀ {i} → OrdI B → Ordᴸ i
    ψL {i} zero      = Ω i
    ψL {i} (suc a)   = lim (iter (ψL {i} a +_) zero)
    ψL {i} (lim f)   = lim (λ n → ψL {i} (f n))
    ψL {i} (limᵢ ℓ f) with D ℓ i
    ... | pen r b = limᵢ r (λ y → ψL {i} (f (b (outL i r y))))
    ... | rise    = lim (λ n → ψL {i} (f (iter (λ x → ψL {ℓ} (f x)) (Ω ℓ) n)))
    ψL {i} (limᴵ f)  = lim (λ n → ψL {i} (f (iter (λ L → ψI (f L)) Λ n)))
    ψL {i} (limB f)  = lim (λ n → ψL {i} (f (iter (λ x → fromLv (ψI (f x))) ΩB n)))
    ψL {i} (up ℓ x)  = ψ {i} x
    ψL {i} (upB b)   = ψLB b

  -- I 层本身: 下一梯级是占位 ⊤, limB/upB 不被使用
  T0 : Set
  T0 = OrdI ⊤
  module I₀ = Tier {⊤} tt (λ _ → tt) (λ _ → Λ) (λ _ → Ω _)

  -- I+1 层
  T1 : Set
  T1 = OrdI T0
  module I₁ = Tier {T0} Ωᴵ reseed I₀.ψI I₀.ψL

  -- ψ_{I+1}: 目标高于 T0 与一切 Lv, 所以这三个折叠从不比较 (`↓` 模式); 只有 limB 节点的链留给 T2
  addT1 : T1 → T1 → T1
  addT1 a zero       = a
  addT1 a (suc b)    = suc (addT1 a b)
  addT1 a (lim f)    = lim (λ n → addT1 a (f n))
  addT1 a (limᵢ ℓ f) = limᵢ ℓ (λ y → addT1 a (f y))
  addT1 a (limᴵ f)   = limᴵ (λ L → addT1 a (f L))
  addT1 a (limB f)   = limB (λ b → addT1 a (f b))
  addT1 a (up ℓ x)   = addLow x where
    addLow : ∀ {k} → Ordᴸ k → T1
    addLow zero    = a
    addLow (suc y) = suc (addLow y)
    addLow (lim f) = lim (λ n → addLow (f n))
    addLow {k} (limᵢ r f) = limᵢ (at k r) (λ y → addLow (f (intoL k r y)))
    addLow {suc k}    (up d y) = addLow y
    addLow {lim f}    (up d y) = addLow y
    addLow {limᴼ k g} (up d y) = addLow y
  addT1 a (upB b)    = a   -- 脚手架: 只在 ψ↓ 的 suc 子句里遇到, 闭项不走到

  ψ₁ᴸ : ∀ {k} → Ordᴸ k → T1
  ψ₁ᴸ zero    = Ωᴵ⁺
  ψ₁ᴸ (suc a) = lim (iter (λ x → addT1 (ψ₁ᴸ a) x) zero)
  ψ₁ᴸ (lim f) = lim (λ n → ψ₁ᴸ (f n))
  ψ₁ᴸ {k} (limᵢ r f) = limᵢ (at k r) (λ y → ψ₁ᴸ (f (intoL k r y)))
  ψ₁ᴸ {suc k}    (up d x) = ψ₁ᴸ x
  ψ₁ᴸ {lim f}    (up d x) = ψ₁ᴸ x
  ψ₁ᴸ {limᴼ k g} (up d x) = ψ₁ᴸ x

  ψ₁₀ : T0 → T1
  ψ₁₀ zero       = Ωᴵ⁺
  ψ₁₀ (suc a)    = lim (iter (λ x → addT1 (ψ₁₀ a) x) zero)
  ψ₁₀ (lim f)    = lim (λ n → ψ₁₀ (f n))
  ψ₁₀ (limᵢ ℓ f) = limᵢ ℓ (λ y → ψ₁₀ (f y))
  ψ₁₀ (limᴵ f)   = limᴵ (λ L → ψ₁₀ (f L))
  ψ₁₀ (limB f)   = zero   -- T0 的 limB 不使用
  ψ₁₀ (up ℓ x)   = ψ₁ᴸ x
  ψ₁₀ (upB _)    = zero

  ψ₁↓ : T1 → T1
  ψ₁↓ zero       = Ωᴵ⁺
  ψ₁↓ (suc a)    = lim (iter (λ x → addT1 (ψ₁↓ a) x) zero)
  ψ₁↓ (lim f)    = lim (λ n → ψ₁↓ (f n))
  ψ₁↓ (limᵢ ℓ f) = limᵢ ℓ (λ y → ψ₁↓ (f y))
  ψ₁↓ (limᴵ f)   = limᴵ (λ L → ψ₁↓ (f L))
  ψ₁↓ (limB f)   = limB (λ b → ψ₁↓ (f b))
  ψ₁↓ (up ℓ x)   = ψ₁ᴸ x
  ψ₁↓ (upB b)    = ψ₁₀ b

  TI TI+1 TI+2 : Ordᴸ zero
  TI   = I₀.ψL {zero} Ωᴵ                                  -- ψ₀(I)
  TI+1 = I₁.ψL {zero} Ωᴵ⁺                                 -- ψ₀(Ω_{I+1})
  TI+2 = lim (λ n → I₁.ψL {zero} (iter ψ₁↓ Ωᴵ⁺ n))        -- ψ₀(Ω_{I+2})

  _ : TI ≡ lim (λ n → ψ⁰ (Ω (iter (λ L → ψᴸ (Ω L)) Λ n)))
  _ = refl
  _ : I₀.ψI Ωᴵ ≡ lim (λ n → ψᴸ (Ω (iter (λ L → ψᴸ (Ω L)) Λ n)))
  _ = refl
  _ : I₀.ψI zero ≡ Λ
  _ = refl
  _ : TI+1 ≡ lim (λ n → I₀.ψL {zero} (iter (λ x → reseed (I₀.ψI x)) Ωᴵ n))
  _ = refl
```

## §4 层 3 要说什么: 编译的否定与证书的类型

**数值检验 (在 `ver` 下).** 只是形状; FGH 在 `n ≥ 2` 时已不能由 `refl` 算完.

```agda
module Numeric where
  open Terms ver
  open ITier ver using (TI)

  _ : FGH T₂ 0 ≡ 1
  _ = refl
  _ : FGH T₂ 1 ≡ 2
  _ = refl
  _ : FGH EBOᵀ 0 ≡ 1
  _ = refl
  _ : FGH EBOᵀ 1 ≡ 2
  _ = refl
  _ : FGH TI 0 ≡ 1
  _ = refl
  _ : FGH TI 1 ≡ 2
  _ = refl
```

**否定 4 (`¬BranchΩ` 的对应物): 穿透分支不能对全部输入量化.** 在目标 1 读 `Ω̂`, 穿透输出的分支遍历一切第 0 层树 `y`, 下一步要比较 `toLv y` 与 1. 对全部 `y` 的正确判决 (哪怕只是结构三歧成立) 是假的: `lim [0,0,…]` 与 1 三者皆否. 所以证书只能对 "好的" 输入量化, 好输入的类从外面给.

```agda
ZeroS : Ordᴸ zero
ZeroS = lim (λ _ → zero)

¬SoundAll : (∀ (y : Ordᴸ zero) → Trichʹ (toLv y) (natL 1)) → ⊥
¬SoundAll h with h ZeroS
... | injᵃ (via (inj₁ _) ())
... | injᵇ (via (_ , ()) _)
... | injᶜ ()
```

**否定 5: 即使没有地板, 单调证据也去不掉.** 分支函数 `f` 只要对每个输入逐点是好树, 链就可能不步进: `f 1 = 1`, 其余 `f y = 0`, 链点在 `1, ω̂, 1, ω̂, …` 之间振荡. 所以现行 `Goodᴸ` 的 `mE`/`mo` 类字段不是地板带来的负担, 是折叠本身要的.

```agda
oscF : Ordᴸ zero → Ordᴸ (suc zero)
oscF (suc zero) = suc zero
oscF _          = zero

module Osc where
  open Fold ver
  oscT : Ordᴸ zero
  oscT = ψ {zero} {suc zero} (limᵢ (inj₁ tt) oscF)

  oscT₀ oscT₁ : Ordᴸ zero
  oscT₀ = ψ {zero} {suc zero} (suc zero)
  oscT₁ = ψ {zero} {suc zero} zero

  _ : oscT ≡ lim (λ n → ψ {zero} {suc zero} (oscF (iter (λ x → ψ {zero} {suc zero} (oscF x)) (suc zero) n)))
  _ = refl
  _ : ψ {zero} {suc zero} (oscF (suc zero)) ≡ oscT₀
  _ = refl
  _ : ψ {zero} {suc zero} (oscF oscT₀) ≡ oscT₁
  _ = refl

  not-step : ¬ (toLv oscT₀ ⊑ toLv oscT₁)
  not-step h with h (2 , inj₁ tt)
  ... | via (inj₁ _) ()
  ... | via (inj₂ ()) _
```

**证书的形状 (只有类型).** `Good` 是对树的递归谓词 (`G`), 不是 mutual inductive: `limᵢ` 节点上对好输入量化, 加单调; `lim` 节点加步进. 观测前序 `Obs` 与第 0 层的 `Base` 是参数. `Run i x` 说 "目标 `i` 读 `x` 时每个判决为真". 这就是现行 `Goodᴸ`/`Goodᴺ` 去掉 `ŝ`/`ĉᴸ`、地板、`FlrLab` 之后剩下的东西; 下面的 `Close` 是单一的闭包定理.

```agda
Sound : ∀ {j i} → Verdict j i → Set
Sound {j} {i} (pen r b) = j ≅ at i r
Sound {j} {i} rise      = i ≺ j ⊎ i ≅ j

module Cert (D : Oracle)
  (G   : ∀ {k} → Ordᴸ k → Set)                 -- 好输入 (调用方给定)
  where
  open Fold D

  -- `up` 透明, 所以证书也按 (层号, 树) 递归
  data Run (i : Lv) : ∀ k → Ordᴸ k → Set where
    rz : ∀ {k} → Run i k zero
    rs : ∀ {k a} → Run i k a → Run i k (suc a)
    rl : ∀ {k f} → (∀ n → Run i k (f n)) → Run i k (lim f)
    rp : ∀ {k r f r′ b} → D (at k r) i ≡ pen r′ b → Sound (D (at k r) i) →
         (∀ y → G y → Run i k (f (intoL k r (b y)))) → Run i k (limᵢ r f)
    rc : ∀ {k r f} → D (at k r) i ≡ rise → Sound (D (at k r) i) →
         G (Ω (at k r)) →
         (∀ x → G x → Run (at k r) k (f (intoL k r x))) →
         (∀ x → G x → G (ψ {at k r} (f (intoL k r x)))) →
         (∀ x → G x → Run i k (f (intoL k r x))) → Run i k (limᵢ r f)
    ru : ∀ {k} {d : Dn k} {x : DnT k d} → Run i (down k d) (outD k d x) → Run i k (up d x)

  -- 单一闭包定理的类型: 证书 `Run` 蕴含输出为好
  Close : Set
  Close = ∀ i k (x : Ordᴸ k) → Run i k x → G (ψ {i} x)
```

**一块被证实的证据: 有限层.** 判决 `ver` 在有限数上是对的 (`ver-sound`), 不用任何假设. 这是目前唯一无条件证实的判决片段. 它说明 `ψ₀(Ω_n)` 系列 (BO 之下) 的派发证据是定理; 一旦比较涉及 ℕ-极限层号 (第一次出现见验收 `first-nonnat`), 证据就要从链上来.

```agda
same-≅ : ∀ {a b} → IsNat a → IsNat b → same a b ≡ true → a ≅ b
same-≅ nz     nz     e = z≅
same-≅ (ns {a = a} i) (ns {a = b} j) e = s≅ (same-≅ {a} {b} i j e)

≅-same : ∀ {a b} → IsNat a → IsNat b → a ≅ b → same a b ≡ true
≅-same nz     nz     z≅     = refl
≅-same (ns {a = a} i) (ns {a = b} j) (s≅ e) = ≅-same {a} {b} i j e

0≺s : ∀ {a} → IsNat a → zero ≺ suc a
0≺s nz     = via (inj₁ tt) z≅
0≺s (ns i) = via (inj₂ (pth (0≺s i))) (prf (0≺s i))

s≺-or : ∀ {a b} → IsNat a → IsNat b → a ≺ b → (suc a ≺ b) ⊎ (suc a ≅ b)
s≺-or i (ns j) (via (inj₁ _) e) = inj₂ (s≅ e)
s≺-or i (ns j) (via (inj₂ r) e) with s≺-or i j (via r e)
... | inj₁ (via r′ e′) = inj₁ (via (inj₂ r′) e′)
... | inj₂ e′          = inj₁ (via (inj₁ tt) e′)

ver-sound : ∀ {j i} → IsNat j → IsNat i → Sound (ver j i)
ver-sound nz     nz = inj₂ z≅
ver-sound (ns x) nz = inj₁ (0≺s x)
ver-sound {j} {suc i} x (ns y) with same j i in eq
... | true  = same-≅ x y eq
... | false with ver j i | ver-sound x y
...   | pen r b | h = h
...   | rise    | inj₁ q = s≺-or y x q
...   | rise    | inj₂ e with trans′ (sym (≅-same x y (≅-sym e))) eq
...     | ()
```

## §5 对现行工作的启示 (判决)

**B.1 机器是否消失.** 定义层面消失: 前缀塔、地板、非紧界、帧、`ŝ`/`ĉᴸ`、`force`. 原因不是新数学, 而是 `Ordᴵ` 之外多了 `limᴼ` 后, 树有了可以停留的层 (`L₁`), 且判决从环境里搬了出去: 现行机器的一大部分是为 `<ᴵ-dec` 要一个 "含目标与全部地板的字面层" 而存在的. 逐项比较无不一致 (验收 §3, 列出的宽深度内), 但这是有限证据, 且依赖 `ver`.

**B.2 难度去了哪.** 见报告的表. 判决 `D` 之外的定义约 145 行, 判决本身无证; 现行形态的第一阶段定义 ≈300 行 (不含 BTBO 的 ≈230), 但现行的 `<ᴵ-dec` 派发在其环境内是**定理**, 而这里不是. 证书: `Run` 6 个构造子 + 未定的 `G`; 现行 `Goodᴸ.gc` 11 个字段加地板标签. 省掉的是 `FlrLab`/`FW`/`Top`/`bound-≅`/`AlignD`/`≅ᴬ`, 留下的是链支配、单调、比较的真实性.

**B.3 降维打击.** 见结论 5. 不报告乐观判断.

**B.4 回传.** (i) `HΩ̂` 的深度量词是塔的伪影: 新形态里它是 `G Ω̂` 加 `Close`, 没有 `d`. 现行形态上可试的等价陈述是对 `Syn` 归纳而不是对 `d` 量化 (纸面, 未证). (ii) 地板不是语义: 三处验收路径上无地板的折叠都对, 所以 `fb K` 这类修正的方向是对的, 地板应只服务于 `<ᴵ-dec` 的环境, 不应影响输出值, 这可以作为检验修正的判据. (iii) `not-step` 说明 `mE`/`mo` 不是地板带来的, 不必指望简化掉. (iv) `diff` 比较器可直接用于现行树 (换 `strip`/`lim` 的模式) 找第一个偏差点, 比逐条 `kind` 省事. 回传**不包括**判决设计本身: 现行形态没有 `L₁`, 搬过去等于替换, 不是修补.

**脚手架与内容.** 内容: `Lv`/`Ordᴸ`/`Ω`/`toLv`/`add`, `Fold`, `ψ↓`, `≅`/`tr`/`res`/`<-dec`, `dir-L₁`, `¬WF-L₁`, `noBT`, `¬SoundAll`, `not-step`, `ver-sound`, `up-*`, `chainΩ̂`, `Run`/`Close` (类型). 脚手架: `cast`/`same`/`reify`/`ver`/`search`, I 层的占位 `B = ⊤` 与 `limB` 不用的子句, `addT1` 的 `upB` 子句, `ψ₁₀` 的占位. `ψ₀(Ω_{I+n})` 只写到 `n = 2`, 且 `I+2` 只有链的形状; 对 `n` 的一般塔要与 `Lv` 同构的路径理论, 未写.
