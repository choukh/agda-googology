# 终局 (三): 真正的塔. 裸层号上除一族 `HS` 外全部无条件

> 不含记号. 结论写在 [EBOTop](EBOTop.lagda.md). 世界是 [InaccTreeBase](InaccTreeBase.lagda.md) 的 `Lv`/`Ordᴸ` 与 [InaccFloorTree](InaccFloorTree.lagda.md) 的折叠 `PF S`. `S : Sib` 是**参数**, 也是这条路线上定义一侧还没有解决的东西. 层上的事实 (塔的形状, 不动点) 不提 `S`; 折叠上的事实对**一切** `S` 成立.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EBOTopRaw where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase
open import OCF.Align.InaccFloorTree using (Sib; Mode; fin; lt; sib; upM; verdict; chM; natL; Sz; module PF)
import OCF.Align.EBOTopStage as St
open St using (O₀; Stage; module Top; tow)
```

## §1 塔与不动点: 无条件, 不提折叠

$\Lambda=\sup_n L_n$, $L_0=0$, $L_{n+1}=\Omega_{L_n}$ 读成层号. `next` 里**没有折叠**: 这是它与 BTBO 的 `ordᴰ ∘ ψ₀ ∘ Ω` 唯一的差别, 也是层号必须是裸宇宙的原因.

```agda
next : Lv → Lv
next ℓ = toLv (Ω ℓ)

tower : ℕ → Lv
tower = tow zero next

Λ : Lv
Λ = lim tower

-- 前几项, refl
_ : tower 1 ≡ suc zero
_ = refl

_ : tower 2 ≡ limᴼ zero toLv
_ = refl

_ : tower 3 ≡ limᴼ zero (λ y → next (toLv y))
_ = refl

-- 分支 $\ell\sqsubseteq\Omega_\ell$, 对一切裸层号
infl : ∀ ℓ → ℓ ⊑ next ℓ
infl (suc k)    (inj₁ _) = via (inj₁ (inj₁ tt)) (≅-refl k)
infl (suc k)    (inj₂ r) = via (inj₁ (inj₂ r)) (≅-refl _)
infl (lim f)    (n , r) with infl (f n) r
... | via q e = via (n , q) e
infl (limᴼ k g) (inj₁ (inj₁ _)) = via (inj₁ (inj₁ tt)) (≅-refl k)
infl (limᴼ k g) (inj₁ (inj₂ r)) = via (inj₁ (inj₂ r)) (≅-refl _)
infl (limᴼ k g) (inj₂ (x , r)) with infl (g x) r
... | via q e = via (inj₂ (x , q)) e

ub : ∀ (f : ℕ → Lv) n → f n ⊑ lim f
ub f n r = via (n , r) (≅-refl _)
```

**不动点.** 关系是层序 $\sqsubseteq$ 的两个方向 (`≃`). 它不是结构互模拟 (`¬≅`), 也不是 $\prec$: 两边**互不** $\prec$ (`¬≺₁`, `¬≺₂`), 所以结构三歧在不动点上不成立 (`¬tri-fix`). 这正是 `noBT` 的现象落在 $\Lambda$ 上.

```agda
_≃_ : Lv → Lv → Set
a ≃ b = (a ⊑ b) × (b ⊑ a)

Ω-Λ⊑ : ∀ {f : ℕ → Lv} {b} → (∀ n → next (f n) ⊑ b) → next (lim f) ⊑ b
Ω-Λ⊑ H (n , r) = H n r

fixpoint : next Λ ≃ Λ
fixpoint = Ω-Λ⊑ (λ n → ub tower (suc n)) , infl Λ

¬≅ : next Λ ≅ Λ → ⊥
¬≅ (l≅ h) with h 0
... | ()

data AccL (a : Lv) : Set where
  acc : (∀ {c} → c ≺ a → AccL c) → AccL a

accL : ∀ a {c} → c ≺ a → AccL c
accL (suc k)    (via (inj₁ _) e)        = acc (λ q → accL k (≺-respʳ q e))
accL (suc k)    (via (inj₂ r) e)        = accL k (via r e)
accL (lim f)    (via (n , r) e)         = accL (f n) (via r e)
accL (limᴼ k g) (via (inj₁ (inj₁ _)) e) = acc (λ q → accL k (≺-respʳ q e))
accL (limᴼ k g) (via (inj₁ (inj₂ r)) e) = accL k (via r e)
accL (limᴼ k g) (via (inj₂ (x , r)) e)  = accL (g x) (via r e)

≺-irrefl : ∀ {a} → a ≺ a → ⊥
≺-irrefl {a} = go (acc (accL a)) where
  go : ∀ {a} → AccL a → a ≺ a → ⊥
  go (acc h) q = go (h q) (≺-respʳ q (≅-refl _))

⊑-step : ∀ {a b c} → a ≺ b → b ⊑ c → a ≺ c
⊑-step (via r e) σ = ≺-respˡ e (σ r)

¬≺₁ : next Λ ≺ Λ → ⊥
¬≺₁ q = ≺-irrefl (⊑-step q (infl Λ))

¬≺₂ : Λ ≺ next Λ → ⊥
¬≺₂ q = ≺-irrefl (⊑-step q (proj₁ fixpoint))

¬tri-fix : Trichʹ (next Λ) Λ → ⊥
¬tri-fix (injᵃ q) = ¬≺₁ q
¬tri-fix (injᵇ q) = ¬≺₂ q
¬tri-fix (injᶜ e) = ¬≅ e
```

**$\Omega$-共尾性: 这个 `next` 真的越过了第 0 层.** 第 $k$ 层的每棵树的层号都在 $\Omega_{k+1}$ 的层号之下. 这是壁垒要的 "$\Omega$-共尾元"; 所以下面不能有全局比较 (`EBOTopBarrier`).

```agda
cof : ∀ k (t : Ordᴸ k) → toLv t ⊑ next (suc k)
cof k t r = via (inj₂ (t , r)) (≅-refl _)
```

## §2 塔的形状: 每一项都是第 0 层上的一条对角线

`G n y` $=\Omega^{(n)}_y$, 塔的第 $n+2$ 项就是 $\mathrm{limᴼ}\ 0\ (G\,n)$. 所以**塔本身从不提参数层 $\ge1$**, 但它的分支马上就提 (§5).

```agda
G : ℕ → Ordᴸ zero → Lv
G zero    y = toLv y
G (suc n) y = next (G n y)

tower-form : ∀ n → tower (suc (suc n)) ≡ limᴼ zero (G n)
tower-form zero    = refl
tower-form (suc n) = cong next (tower-form n)

G-one : ∀ n → G n (suc zero) ≡ tower (suc n)
G-one zero    = refl
G-one (suc n) = cong next (G-one n)

-- 分支: 下标的参数层是任意的
G₁-suc : ∀ (y : Ordᴸ zero) → G 1 (suc y) ≡ limᴼ (toLv y) toLv
G₁-suc y = refl

G₁-nat : G 1 (suc (suc zero)) ≡ limᴼ (suc zero) toLv
G₁-nat = refl
```

## §3 折叠: 第 0 层的读出, 脊上的步进

`natT k` 是 $k$ 的树, `St′ k` 是 $k+1$ 的树.

```agda
natT : ℕ → Ordᴸ zero
natT zero    = zero
natT (suc n) = suc (natT n)

St′ : ℕ → Ordᴸ zero
St′ k = suc (natT k)

toLv-natT : ∀ k → toLv (natT k) ≡ natL k
toLv-natT zero    = refl
toLv-natT (suc k) = cong suc (toLv-natT k)

rd : Ordᴸ zero → O₀
rd zero        = O₀.zero
rd (suc a)     = O₀.suc (rd a)
rd (lim f)     = O₀.lim (λ n → rd (f n))
rd (limᵢ () f)
rd (up () x)

module Raw (S : Sib) where
  open PF S

  ψ₀ : ∀ {k} → Ordᴸ k → Ordᴸ zero
  ψ₀ = ψⁿ 0

  X : Lv → Ordᴸ zero
  X ℓ = ψ₀ (Ω ℓ)

  x : ℕ → Ordᴸ zero
  x n = X (tower n)

  EBOᵀ : Ordᴸ zero
  EBOᵀ = X Λ

  -- 闭项: 对任何 S 都有定义, 且是 x 的极限 (refl)
  EBO-lim : EBOᵀ ≡ lim x
  EBO-lim = refl

  big : ℕ → ℕ
  big = St.FGH (rd EBOᵀ)

  -- 目标 0: 判决不被问, 这一步是规则 6 的链, 目标 0
  chain : (Ordᴸ zero → Lv) → ℕ → Ordᴸ zero
  chain g = iter (λ y → X (g y)) (suc zero)

  rise-diag : ∀ g → X (limᴼ zero g) ≡ lim (λ m → X (g (chain g m)))
  rise-diag g = refl

  x-form : ∀ n → x (suc (suc n)) ≡ lim (λ m → X (G n (chain (G n) m)))
  x-form n = cong X (tower-form n)

  -- 脊: $x_n$ 就是 $x_{n+1}$ 的第 0 项 (除 n=0 的头以外字面成立)
  head : ∀ n → X (G n (suc zero)) ≡ x (suc n)
  head n = cong X (G-one n)

  spine : ∀ n → rd (x n) St.⊑⁰ rd (x (suc n))
  spine zero h = St.≺l 0 h
  spine (suc n) {c} h =
    subst (λ t → c St.≺⁰ rd t) (sym (x-form n))
      (St.≺l 0 (subst (λ t → c St.≺⁰ rd t) (sym (head n)) h))
```

**目标的字面上界 (对一切 `S`, 一切 `m`).** 第 $i$ 层上任何折叠输出的层号都包含 $i$ 的全部前驱. 所以链的第 $x$ 点上, 目标 $i$ 与节点层 $j\prec$ `toLv x` 有字面的公共上界 `toLv x`: 这是把 `Sib` 换成局部比较的前提 (判断, 比较本身没有写; 见 [EBOTop](EBOTop.lagda.md)).

```agda
  ψ-bound : ∀ {k i} (m : Mode k i) (t : Ordᴸ k) → i ⊑ toLv (ψᵖ m t)
  ψ-bound {i = i} m zero r = infl i r
  ψ-bound m (suc a) r with ψ-bound m a r
  ... | via q e = via (1 , q) e
  ψ-bound m (lim f) r with ψ-bound m (f 0) r
  ... | via q e = via (0 , q) e
  ψ-bound {k} {i} m (limᵢ r₀ f) r with verdict S m r₀
  ... | pen r′ b with ψ-bound m (f (intoL k r₀ (b (outL i r′ (intoL i r′ zero))))) r
  ...   | via q e = via (inj₂ (zero , q)) e
  ψ-bound {k} {i} m (limᵢ r₀ f) r | rise with ψ-bound m (f (intoL k r₀ (Ω (at k r₀)))) r
  ...   | via q e = via (0 , q) e
  ψ-bound {suc k}    m (up d x) r = ψ-bound (upM (suc k) d m) x r
  ψ-bound {lim f}    m (up d x) r = ψ-bound (upM (lim f) d m) x r
  ψ-bound {limᴼ k g} m (up d x) r = ψ-bound (upM (limᴼ k g) d m) x r
```

## §4 残差: 这条路线上剩下的只有一句话

`Residual` 是把这个世界做成 `Stage` 还缺的全部字段, **都是假设**. `toStage` 说它们够了; `res→fam`, `fam→res` 说它们等价于一族 `HS`:

$$\forall n.\ \mathrm{HS}(\psi_0(\Omega_{L_n}))$$

所以对裸层号这条路线, 阶段定理要交付的**恰好**是 `Family`, 其余的 (`infl`, `ub`, `Ω-Λ`, `spine`, 不动点, 闭项本身) 都已经是定理.

```agda
  record Residual : Set₁ where
    field
      GL  : Lv → Set
      GT  : ∀ {ℓ} → Ordᴸ ℓ → Set
      gz  : GL zero
      gΩ  : ∀ {ℓ} → GL ℓ → GT (Ω ℓ)
      gc  : ∀ {ℓ} {t : Ordᴸ ℓ} → GT t → St.HS (rd (ψ₀ t))
      gf  : ∀ {ℓ} {t : Ordᴸ ℓ} → GT t → GL (toLv t)
      gΛ  : ∀ (f : ℕ → Lv) → (∀ n → f n ≡ tower n) → GL (lim f)

  Family : Set
  Family = ∀ n → St.HS (rd (x n))

  toStage : Residual → Stage
  toStage R = record
    { Lv = Lv ; Tr = Ordᴸ ; base = zero ; out = rd ; Ω = Ω ; ψ₀ = ψ₀
    ; GoodL = GL ; GoodT = GT
    ; seed = zero ; good-seed = gz
    ; good-Ω = gΩ ; cert = gc
    ; feed = λ t _ → toLv t
    ; good-feed = λ t g → gf g
    ; _⊑_ = _⊑_
    ; infl = λ {ℓ} _ → infl ℓ
    ; lub = λ f _ → lim f
    ; ub = λ f _ n → ub f n
    ; lub-Ω = λ f _ → refl
    ; good-Λ = gΛ _ (tow-eq)
    ; Ω-Λ = λ b H → Ω-Λ⊑ H
    } where
    open Residual R
    Twr : ℕ → Σ Lv GL
    Twr = tow (zero , gz) (λ p → next (proj₁ p) , gf (gΩ (proj₂ p)))
    tow-eq : ∀ n → proj₁ (Twr n) ≡ tower n
    tow-eq zero    = refl
    tow-eq (suc n) = cong next (tow-eq n)

  res→fam : Residual → Family
  res→fam R n = gc (gΩ (go n)) where
    open Residual R
    go : ∀ n → GL (tower n)
    go zero    = gz
    go (suc n) = gf (gΩ (go n))

  module FromFamily (F : Family) where
    data GLᶠ : Lv → Set where
      tw : ∀ n → GLᶠ (tower n)
      lm : ∀ k (f : ℕ → Lv) → (∀ n → f n ≡ tower (n +ᴺ k)) → GLᶠ (lim f)

    data GTᶠ : ∀ {ℓ} → Ordᴸ ℓ → Set where
      gtΩ : ∀ {ℓ} → GLᶠ ℓ → GTᶠ (Ω ℓ)

    hs-at : ∀ {ℓ n} → ℓ ≡ tower n → St.HS (rd (X ℓ))
    hs-at {n = n} refl = F n

    step-at : ∀ {a b n} → a ≡ tower n → b ≡ tower (suc n) → rd (X a) St.⊑⁰ rd (X b)
    step-at {n = n} refl refl = spine n

    gcᶠ : ∀ {ℓ} {t : Ordᴸ ℓ} → GTᶠ t → St.HS (rd (ψ₀ t))
    gcᶠ (gtΩ (tw n))     = F n
    gcᶠ (gtΩ (lm k f e)) = St.hl (λ n → hs-at (e n)) (λ n → step-at (e n) (e (suc n)))

    gfᶠ : ∀ {ℓ} {t : Ordᴸ ℓ} → GTᶠ t → GLᶠ (toLv t)
    gfᶠ (gtΩ (tw n))     = tw (suc n)
    gfᶠ (gtΩ (lm k f e)) = lm (suc k) (λ n → next (f n))
      (λ n → trans (cong next (e n)) (cong tower (sym (+-suc n k))))

    resᶠ : Residual
    resᶠ = record
      { GL = GLᶠ ; GT = GTᶠ ; gz = tw 0 ; gΩ = gtΩ ; gc = gcᶠ ; gf = gfᶠ
      ; gΛ = λ f e → lm 0 f (λ n → trans (e n) (cong tower (sym (+-identityʳ n)))) }

  fam→res : Family → Residual
  fam→res F = FromFamily.resᶠ F

  -- 条件定理: Family 给出闭项的证书, FGH, 不动点
  module Finish (F : Family) where
    stage : Stage
    stage = toStage (fam→res F)

    EBO-cert : St.HS (Top.EBOᵀ stage)
    EBO-cert = Top.EBO-HS stage

    ans : ℕ → ℕ
    ans = Top.big stage

    -- 条件闭项就是无条件的 `EBOᵀ`: 证书不改变树
    term-same : Top.EBOᵀ stage St.≅⁰ rd EBOᵀ
    term-same = St.l≅ λ n → subst (λ ℓ → rd (X (Stage.L stage n)) St.≅⁰ rd (X ℓ)) (L-eq n) (St.≅⁰-refl _)
      where
      L-eq : ∀ n → Stage.L stage n ≡ tower n
      L-eq zero    = refl
      L-eq (suc n) = cong next (L-eq n)
```

## §5 塔里实际问到了什么

下面是 refl 的路径, 对一切 `S` 成立, 不读记号. 它回答 "能不能只用一个窄片段": **不能在层号或目标上窄**.

**参数层 $\ge1$ 的 `limᴼ` 躲不开.** $x_3$ 的第 1 项是 $T(x_2)$, 其中 $T\,y=\psi_0(\Omega_{\Omega_y})$. 沿 $x_2$ 的基本列往下走, 第 $(1,0,0,2)$ 项就是 $T(2)=\psi_0(\Omega_{\Omega_2})$, 它的下标就是 `limᴼ 1 toLv`. `no-Ω₂` 要的层号就在这里.

```agda
  T₁ : Ordᴸ zero → Ordᴸ zero
  T₁ y = X (G 1 y)

  T₁-suc : ∀ y → T₁ (suc y) ≡ X (limᴼ (toLv y) toLv)
  T₁-suc y = refl

  T₁-lim : ∀ f → T₁ (lim f) ≡ lim (λ n → T₁ (f n))
  T₁-lim f = refl

  -- 第 m 项
  at₃ : ℕ → Ordᴸ zero
  at₃ m = T₁ (chain (G 1) m)

  x₃-form : x 3 ≡ lim at₃
  x₃-form = refl
```

**第 $k$ 个分支的链走目标 $k$.** $T(k+1)$ 的第一个节点是第 $k$ 层, 目标 0 时 `rise`, 链的折叠目标是 $k$. 所以 $\psi_k$ 对一切 $k$ 都出现, 不是某一站的特例. $k$ 是字面自然数时走 `fin`, 不问 `S` (`silent-1`). $k$ 一旦不是字面自然数, 模式就是 `lt`, 过 `up` 之后变 `sib`, 下面的比较全部问 `S` (`asked`, `query`).

路径 (都是 `refl`, 有限条, 对变量 `S`): $x_3[1,0,0,2]=T(2)$, $x_3[1,0,1,2,2,1]=T(\omega'+1)$, 其中 $\omega'=\psi_0(1)$. 所以 $x_3$ 里**字面地**有 $\psi_0(\Omega_{\Omega_2})$ 与 $\psi_0(\Omega_{\Omega_{\omega+1}})$, 后者的链的目标是 $\omega$. `S` 不是绕得开的.

```agda
  rise-k : ∀ k → T₁ (St′ k) ≡ X (limᴼ (natL k) toLv)
  rise-k k = cong (λ a → X (limᴼ a toLv)) (toLv-natT k)

  walkT : List ℕ → Ordᴸ zero → Ordᴸ zero
  walkT []       t = t
  walkT (n ∷ ns) (lim f) = walkT ns (f n)
  walkT (n ∷ ns) t = t

  ω′ : Ordᴸ zero
  ω′ = x 0

  reach-Ω₂ : walkT (1 ∷ 0 ∷ 0 ∷ 2 ∷ []) (x 3) ≡ T₁ (suc (suc zero))
  reach-Ω₂ = refl

  reach-Ωω₁ : walkT (1 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 1 ∷ []) (x 3) ≡ T₁ (suc ω′)
  reach-Ωω₁ = refl

  -- 下标 Ω_{Ω_2} 的层号就是 `no-Ω₂` 要的层号
  level-Ω₂ : G 1 (suc (suc zero)) ≡ toLv (Ω (natL 2))
  level-Ω₂ = refl

  silent-1 : chM (limᴼ (natL 1) toLv) (inj₁ (inj₁ tt)) ≡ fin 1 refl
  silent-1 = refl

  Kω : Lv
  Kω = limᴼ (toLv ω′) toLv

  rω : Pre Kω
  rω = inj₁ (inj₁ tt)

  asked : chM Kω rω ≡ lt rω refl
  asked = refl

  query-mode : ∀ (y : Ordᴸ (toLv ω′)) → upM Kω y (lt rω refl) ≡ sib
  query-mode y = refl

  query : ∀ (y : Ordᴸ (toLv ω′)) {k′} (r : Pre k′) → verdict S (sib {k′} {toLv ω′}) r ≡ Sz S (at k′ r) (toLv ω′)
  query y r = refl
```

**这里的树与已有的站点是同一棵.** `TΩΩ` 是 [InaccFloorTree](InaccFloorTree.lagda.md) 的起点, 第 1–5 站都在它的基本列之下 ([InaccFloorAccept](InaccFloorAccept.lagda.md) 的路径 `s4`–`s7`, `p₁`, 有限条). 所以**到目前为止的全部站点都在塔的第 3 项之内**.

```agda
  same-TΩΩ : x 3 ≡ TΩΩ
  same-TΩΩ = refl

  reach-T₅ : walkT (1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ []) (x 3) ≡ T₅
  reach-T₅ = refl

  -- x₂ 走到下标 ω·2+2. 这里 `S` 为变量时 `diff 11 3` 不归约 (探针, 不是编译的否定)
  reach-x₂ : walkT (1 ∷ 1 ∷ 2 ∷ 3 ∷ 2 ∷ []) (x 2) ≡ X (toLv (suc (suc (ω′ + ω′))))
  reach-x₂ = refl
```

**`S` 确实改变树.** 取 $y_1$ 为 $T(\omega'+1)$ 的第 1 个链点, 它的第 2 项就是下面的 `node`, 目标 $\omega'$, 节点层 1. 这个节点上 `rise` 与 `ver` 给出不同的头 (`kind-rise`, `kind-ver`). 所以这一问是真的. 问题本身不难 ($1<\omega$): 走到这里时分支下标 $2$ 与目标的第 2 项相同, 只是 `sib` 把这条路径丢了.

```agda
  y₀ : Ordᴸ (toLv ω′)
  y₀ = Ω (toLv ω′)

  y₁ : Ordᴸ (toLv ω′)
  y₁ = ψᵖ (lt rω refl) (up y₀ (Ω (toLv y₀)))

  node : Ordᴸ (toLv ω′)
  node = ψᵖ sib (Ω (limᴼ (suc zero) toLv))

  pick : ∀ {k} → Ordᴸ k → ℕ → Ordᴸ k
  pick (lim f) n = f n
  pick t       n = t

  y₁-node : pick y₁ 2 ≡ node
  y₁-node = refl

-- 分类头构造子
kind : ∀ {k} → Ordᴸ k → ℕ
kind zero       = 0
kind (suc _)    = 1
kind (lim _)    = 2
kind (limᵢ _ _) = 3
kind (up _ _)   = 4

kind-rise : kind (Raw.node (λ _ _ → rise)) ≡ 2
kind-rise = refl

kind-ver : kind (Raw.node ver) ≡ 3
kind-ver = refl
```

## §6 再往下一层: 只提第 0 层输入的等价陈述

`Family` 的第 $n+2$ 项是第 0 层上的一条对角线 (`x-form`). 所以终点可以写成**完全不提不可数层号的陈述**: 对每个 $n$, 映射 $T_n\,y=\psi_0(\Omega^{(n+1)}_y)$ 在一个含 1 的好输入集上保持 `HS`, 单调, 膨胀. 这正是 [Diagonal](Diagonal.lagda.md) 的形状, `n = 0` 时它的内容是 [Uniform](Uniform.lagda.md) 的 `Uniform` 与 `Ψ⁰-mono`. 这是条件定理 `family-from`.

```agda
module Reduce (S : Sib) where
  open Raw S

  Tn : ℕ → Ordᴸ zero → Ordᴸ zero
  Tn n y = X (G n y)

  record DiagN (n : ℕ) : Set₁ where
    field
      Gd   : Ordᴸ zero → Set
      g1   : Gd (suc zero)
      gup  : ∀ {y} → Gd y → Gd (Tn n y)
      hs   : ∀ {y} → Gd y → St.HS (rd (Tn n y))
      infl₀ : rd (natT 1) St.⊑⁰ rd (Tn n (natT 1))
      mono : ∀ {y y′} → Gd y → Gd y′ → rd y St.⊑⁰ rd y′ → rd (Tn n y) St.⊑⁰ rd (Tn n y′)

  module UseDiag {n} (D : DiagN n) where
    open DiagN D

    ch : ℕ → Ordᴸ zero
    ch = chain (G n)

    ch-g : ∀ m → Gd (ch m)
    ch-g zero    = g1
    ch-g (suc m) = gup (ch-g m)

    ch-st : ∀ m → rd (ch m) St.⊑⁰ rd (ch (suc m))
    ch-st zero    = infl₀
    ch-st (suc m) = mono (ch-g m) (ch-g (suc m)) (ch-st m)

    x-HS : St.HS (rd (x (suc (suc n))))
    x-HS = subst (λ t → St.HS (rd t)) (sym (x-form n))
      (St.hl (λ m → hs (ch-g m)) (λ m → mono (ch-g m) (ch-g (suc m)) (ch-st m)))

  family-from : St.HS (rd (x 0)) → St.HS (rd (x 1)) → (∀ n → DiagN n) → Family
  family-from h₀ h₁ D zero          = h₀
  family-from h₀ h₁ D (suc zero)    = h₁
  family-from h₀ h₁ D (suc (suc n)) = UseDiag.x-HS (D n)
```

**一步闭包就够了 (条件定理).** 如果好的层号对 `next` 封闭, 第 0 层的好输入的层号是好的, 那么全部塔高一次得到. 所以**塔的高度不是新的工作**: 第 3 项 $x_3$ 是决定性的一站, 只要它的证明走的是 `next` 的闭包而不是特例.

```agda
G-good : (GL : Lv → Set) (Gd : Ordᴸ zero → Set) →
         (∀ {y} → Gd y → GL (toLv y)) → (∀ {ℓ} → GL ℓ → GL (next ℓ)) →
         ∀ n {y} → Gd y → GL (G n y)
G-good GL Gd a c zero    g = a g
G-good GL Gd a c (suc n) g = c (G-good GL Gd a c n g)
```

## §7 必要性: `Family` 逼出第 $k$ 层目标的证书, 对一切 $k$

上面的路径是有限条. 这里是对一切 $k$ 的定理: $x_3$ 的第 $(1,0,0,k+1)$ 项就是 $\psi_0(\Omega_{\Omega_{k+1}})$ (`reach-k`), 它的基本列是目标 $k$ 的链 $y_{m+1}=\psi_k(\Omega_{y_m})$ 回灌下标 (`X-Kk`). `HS` 沿基本列遗传 (`HS-walk`). 所以 `Family` **蕴含** 目标 $k$ 的链上每一点的层号都给出 `HS` 的输出, 并且相邻步进 (`must`, `must-step`). 这回答了 "能不能只做目标 0 或 1": **不能**. 这是编译过的定理, 对一切 `S`.

```agda
module Must (S : Sib) where
  open Raw S
  open PF S using (ψᵖ)

  ω′-nat : ∀ k → iter (natT 1 +_) zero k ≡ natT k
  ω′-nat zero    = refl
  ω′-nat (suc k) = go (iter (natT 1 +_) zero k) k (ω′-nat k) where
    add-suc : ∀ m → natT 1 + natT m ≡ natT (suc m)
    add-suc zero    = refl
    add-suc (suc m) = cong suc (add-suc m)
    go : ∀ t k → t ≡ natT k → natT 1 + t ≡ natT (suc k)
    go _ k refl = add-suc k

  reach-k : ∀ k → walkT (1 ∷ 0 ∷ 0 ∷ suc k ∷ []) (x 3) ≡ T₁ (natT (suc k))
  reach-k k = cong T₁ (ω′-nat (suc k))

  HS-walk : ∀ p (t : Ordᴸ zero) → St.HS (rd t) → St.HS (rd (walkT p t))
  HS-walk []       t       h = h
  HS-walk (n ∷ ns) zero    h = h
  HS-walk (n ∷ ns) (suc a) h = h
  HS-walk (n ∷ ns) (lim f) (St.hl g st) = HS-walk ns (f n) (g n)
  HS-walk (n ∷ ns) (limᵢ () f) h
  HS-walk (n ∷ ns) (up () y) h

  Kk : ℕ → Lv
  Kk k = limᴼ (natL k) toLv

  chk : ∀ k → ℕ → Ordᴸ (natL k)
  chk k = iter (λ y → ψᵖ (chM (Kk k) (inj₁ (inj₁ tt))) (up y (Ω (toLv y)))) (Ω (natL k))

  X-Kk : ∀ k → X (Kk k) ≡ lim (λ m → X (toLv (chk k m)))
  X-Kk k = refl

  HS-Kk : Family → ∀ k → St.HS (rd (X (Kk k)))
  HS-Kk F k = subst (λ t → St.HS (rd t)) (trans (reach-k k) (rise-k k)) (HS-walk (1 ∷ 0 ∷ 0 ∷ suc k ∷ []) (x 3) (F 3))

  must : Family → ∀ k m → St.HS (rd (X (toLv (chk k m))))
  must F k m with HS-Kk F k
  ... | St.hl g _ = g m

  must-step : Family → ∀ k m → rd (X (toLv (chk k m))) St.⊑⁰ rd (X (toLv (chk k (suc m))))
  must-step F k m with HS-Kk F k
  ... | St.hl _ st = st m
```
