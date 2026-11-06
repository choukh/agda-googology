# X₁ 上叠层, 否定一路 (二): 叠层后哪些比较有公共上界

> 不含记号. 入口 [NegX1Up](NegX1Up.lagda.md). 本篇**不依赖**构造一路的接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 在 $X_1$ 上叠层 (`NegX1UpEmb.ofU x` $=X_1\oplus x$) 之后, 上层折叠的留/坍缩要比较种类的层号与目标. 种类分两类 (底种类, 新种类), 目标也分两类 (可数层号 `ofC t`, 叠层 `ofU y`). 哪些对有字面公共上界, 哪些没有? 对照 [NegPathOutCmp](NegPathOutCmp.lagda.md) 的 `cmp-bound`, `no-exact-c₁`.
>
> **结果.** 层号的序是 [Fab4LOm](Fab4LOm.lagda.md) 的字面子层号 `⊑ᴸ`.
>
> 1. **`base⊏U` (定理, 对一切 $x$, 一切底种类).** 底种类的层号字面严格在 $X_1$ 之下, 从而在一切叠层 `ofU y` 之下 (`X₁⊑U`). 推论 **`exact-keep-base`**: 目标是任一叠层 `ofU y` 时, "留" 对底种类是精确的 (`Exact`), 不要世界, 不要证据.
> 2. **`base⊏new` (定理).** 底种类与新种类 (层号 `ofU z`) 字面可比: 底种类严格在下. "$X_1$ 的种类与 `ls X₁` 的新种类" 这一对**总有**字面公共上界 (新种类自己的层号), 不要证据.
> 3. **`cmp-new` (定理, 构造).** 两个新种类 (或新种类与叠层目标) 的偏移 $z, z'$ 都在合法的偏移 $x$ 之下, 则 `ofU z`, `ofU z'` 字面可比 (同 `cmp-bound`, 公共上界就是折叠所在的层号).
> 4. **`incomp-new` (定理).** 偏移是首项不同的有限项极限 (如 $\lim\mathrm{od}$, $\lim\mathrm{ev}$) 时, 叠层 `ofU (hl od)`, `ofU (hl ev)` 字面不可比. 所以 3 的公共上界不能省.
> 5. **`no-exact-up` (定理, 对一切 $x$).** 叠层后, 底种类 $\kappa(c_1)$ (经 `embB x`) 对可数目标 $t_1$ **没有**精确的决定 (由 `exact→cmp` 与 `incomp-lim`). 叠层不消除 $X_1$ 内部的比较: 若上层折叠直接折到可数目标, 底种类之间的比较仍要 PathOut 的世界与证据.
> 6. **`U-not-cnt` (定理).** 叠层不在任何可数层号之下 (`¬ ofU x ⊑ᴸ ofC c`): 新种类对可数目标只能 "在上".
>
> **小结 (判断, 依据 1-6).** 叠层后共有三种对: (底, 叠层目标), (底, 新) — 字面, 无证据; (新, 新), (新, 叠层目标) — 公共上界是折叠的层号 (同 TySupC 的 `decC`); (底, 可数目标) — 一般无公共上界, 要世界 (5). 若上层折叠只以叠层为目标, 再交给 PathOut 的 `Ψ` 折到可数层号, 第三种对只在 `Ψ` 里出现.
>
> **前提实例.** 1, 2, 6: 无前提. 3: 任一合法 $x$ 及其两个第一位置 (例如 $x=\lim\mathrm{ev}$, $z=z'=0$). 4: `nat-od`, `nat-ev` (`HtTowerNeg`). 5: `Lg-c₁`, `Lg-t₀` 都合法 (`NegPathOutCmp`); 目标 $t_1\sqsubseteq$ `ofU x` (`pt-up`).
>
> **只否定什么.** 4 只否定无公共上界的两个偏移的字面比较; 5 只否定叠层上底种类对可数目标的**精确**决定 (任何蕴含字面可比的判据). **不否定**: 带世界证据的决定 (PathOut 的 `correct₁`); 以叠层为目标的上层折叠 (1-3 是构造). 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX1UpCmp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv; lvl)
open import OCF.Align.TySupIf using (Dc; keep; same; above)
open import OCF.Align.TySupC using (Cd; ofC)
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ; NatH; nat-ev; nat-od)
open import OCF.Align.Fab4LOm
  using (_⊑ᴸ_; _⊏ᴸ_; ⊑self; ⊑suc; ⊑lim; ⊑om; ⊑ᴸ-tr; ls-inj; ll-inj; Exact; κ; t₁; pt₁)
open import OCF.Align.NegPathOutCmp using (CmpL; into; exact→cmp; incomp-lim; u₁; v₁; c₁; s≢z)
open import OCF.Align.PathOutX1 using (X₁; XS₁)
open import OCF.Align.NegX1UpEmb using (ofU; LU; cls; embB; cls-emb; lvl-base; lvl-new; lvl-emb)
```

## §1 底种类在 $X_1$ 之下

可数层号的种类在自己的层号之下 (`posL`); $X_1$ 的种类在 $X_1$ 之下 (`posX₁`).

```agda
posL : ∀ c κ → lvl (ofC c) κ ⊏ᴸ ofC c
posL hz ()
posL (hs c) (inj₁ κ) = ⊑suc (posL c κ)
posL (hs c) (inj₂ _) = ⊑self
posL (hl f) (n , κ) = ⊑lim n (posL (f n) κ)
posL (hΩ () _) _

posX₁ : ∀ κ → lvl X₁ κ ⊏ᴸ X₁
posX₁ (inj₁ _ , inj₁ ())
posX₁ (inj₁ _ , inj₂ _) = ⊑om hz ⊑self
posX₁ (inj₂ c , κ′) = ⊑om c (posL (hs c) κ′)

X₁⊑U : ∀ x → X₁ ⊑ᴸ ofU x
X₁⊑U hz = ⊑self
X₁⊑U (hs x) = ⊑suc (X₁⊑U x)
X₁⊑U (hl f) = ⊑lim 0 (X₁⊑U (f 0))
X₁⊑U (hΩ () _)

base⊏U : ∀ x κ′ {κ} → cls x κ′ ≡ inj₁ κ → ∀ y → lvl (ofU x) κ′ ⊏ᴸ ofU y
base⊏U x κ′ {κ} p y = subst (λ z → z ⊏ᴸ ofU y) (sym (lvl-base x κ′ p)) (⊑ᴸ-tr (posX₁ κ) (X₁⊑U y))
```

"留" 对底种类精确: 目标是任一叠层.

```agda
exact-keep-base : ∀ x y κ′ {κ} → cls x κ′ ≡ inj₁ κ →
  ∀ (κ″ : K (LU y)) (fr : E (LU y) κ″ → E (LU x) κ′) →
  Exact {ofU x} {ofU y} κ′ (keep κ″ fr)
exact-keep-base x y κ′ p κ″ fr = base⊏U x κ′ p y
```

## §2 底种类与新种类: 字面可比

```agda
base⊏new : ∀ x κ₁ κ₂ {κ z} → cls x κ₁ ≡ inj₁ κ → cls x κ₂ ≡ inj₂ z → lvl (ofU x) κ₁ ⊏ᴸ lvl (ofU x) κ₂
base⊏new x κ₁ κ₂ {z = z} p q = subst (λ w → lvl (ofU x) κ₁ ⊏ᴸ w) (sym (lvl-new x κ₂ q)) (base⊏U x κ₁ p z)

-- 新种类的偏移在折叠所在的偏移之下
newPos : ∀ x κ′ {z} → cls x κ′ ≡ inj₂ z → hs z ⊲[ tt ] x
newPos hz κ′ ()
newPos (hs x) (inj₁ κ′) p = hsuc (newPos x κ′ p)
newPos (hs x) (inj₂ _) refl = hself
newPos (hl f) (n , κ′) p = hlim n (newPos (f n) κ′ p)
newPos (hΩ () _) _
```

## §3 新种类之间: 公共上界是折叠的层号

```agda
ofU-mono : ∀ {y x : Cd} → y ⊲[ tt ] x → ofU y ⊑ᴸ ofU x
ofU-mono hself = ⊑self
ofU-mono (hsuc p) = ⊑suc (ofU-mono p)
ofU-mono (hlim n p) = ⊑lim n (ofU-mono p)
ofU-mono (hLim {κ = ()} _ _)

cmp-new : ∀ {z z′ x : Cd} → z ⊲[ tt ] x → z′ ⊲[ tt ] x → LgB x → CmpL (ofU z) (ofU z′)
cmp-new p q l with cmpB p q tt l
... | inj₁ r = inj₂ (ofU-mono r)
... | inj₂ r = inj₁ (ofU-mono r)
```

## §4 可数层号与叠层; 无公共上界的偏移

`Cnt`: 层号里没有 `lΩ`. 字面子层号保 `Cnt`; 可数层号是 `Cnt`; 叠层不是.

```agda
Cnt : LH → Set
Cnt lz = ⊤
Cnt (ls x) = Cnt x
Cnt (ll f) = ∀ n → Cnt (f n)
Cnt (lΩ _ _) = ⊥

cnt⊑ : ∀ {a b} → a ⊑ᴸ b → Cnt b → Cnt a
cnt⊑ ⊑self c = c
cnt⊑ (⊑suc p) c = cnt⊑ p c
cnt⊑ (⊑lim n p) c = cnt⊑ p (c n)
cnt⊑ (⊑om _ _) ()

cntC : ∀ c → Cnt (ofC c)
cntC hz = tt
cntC (hs c) = cntC c
cntC (hl f) = λ n → cntC (f n)
cntC (hΩ () _)

notCntU : ∀ x → ¬ Cnt (ofU x)
notCntU hz ()
notCntU (hs x) c = notCntU x c
notCntU (hl f) c = notCntU (f 0) (c 0)
notCntU (hΩ () _) _

U-not-cnt : ∀ x c → ¬ (ofU x ⊑ᴸ ofC c)
U-not-cnt x c p = notCntU x (cnt⊑ p (cntC c))
```

有限偏移: `ofU` 单射; 叠层在有限偏移的叠层之下, 只能经后继链与 $X_1$ 的分支, 而分支是可数层号.

```agda
ofU-inj : ∀ (x y : Cd) → NatH x → NatH y → ofU x ≡ ofU y → x ≡ y
ofU-inj hz hz _ _ _ = refl
ofU-inj hz (hs y) _ _ ()
ofU-inj (hs x) hz _ _ ()
ofU-inj (hs x) (hs y) nx ny e = cong hs (ofU-inj x y nx ny (ls-inj e))
ofU-inj (hl _) y () ny e
ofU-inj (hΩ () _) y nx ny e
ofU-inj x (hl _) nx () e
ofU-inj x (hΩ () _) nx ny e

-- ℕ-极限的层号不在 "X₁ 加有限" 之下
ll⋢fin : ∀ (g : ℕ → LH) (y : Cd) → NatH y → (∀ n → ¬ Cnt (g n)) → ¬ (ll g ⊑ᴸ ofU y)
ll⋢fin g hz _ ng (⊑om c p) = ng 0 (cnt⊑ p (cntC (hs c)) 0)
ll⋢fin g (hs y) ny ng (⊑suc p) = ll⋢fin g y ny ng p
ll⋢fin g (hl _) () ng p
ll⋢fin g (hΩ () _) ny ng p
```

```agda
module _ (u v : ℕ → Cd) (nu : ∀ n → NatH (u n)) (nv : ∀ n → NatH (v n)) (ne : ¬ (u 0 ≡ v 0)) where
  private
    half : ∀ (u′ v′ : ℕ → Cd) → (∀ n → NatH (u′ n)) → (∀ n → NatH (v′ n)) → ¬ (u′ 0 ≡ v′ 0) →
           ¬ (ofU (hl u′) ⊑ᴸ ofU (hl v′))
    half u′ v′ nu′ nv′ ne′ p with into p refl
    ... | inj₁ e = ne′ (ofU-inj (u′ 0) (v′ 0) (nu′ 0) (nv′ 0) (cong (λ h → h 0) (ll-inj e)))
    ... | inj₂ (n , q) = ll⋢fin (λ m → ofU (u′ m)) (v′ n) (nv′ n) (λ m → notCntU (u′ m)) q

  incomp-new : ¬ CmpL (ofU (hl u)) (ofU (hl v))
  incomp-new (inj₁ p) = half u v nu nv ne p
  incomp-new (inj₂ p) = half v u nv nu (λ e → ne (sym e)) p

incomp-new-od-ev : ¬ CmpL (ofU (hl odᴴ)) (ofU (hl evᴴ))
incomp-new-od-ev = incomp-new odᴴ evᴴ nat-od nat-ev s≢z
```

## §5 叠层上, 底种类对可数目标: 没有精确的决定

```agda
pt-up : ∀ x → t₁ ⊑ᴸ ofU x
pt-up x = ⊑ᴸ-tr pt₁ (X₁⊑U x)

no-exact-up : ∀ x (d : Dc Lv _⊏ᴸ_ _⊑ᴸ_ (ofU x) t₁ (embB x (κ c₁))) → ¬ Exact (embB x (κ c₁)) d
no-exact-up x d ex =
  incomp-lim u₁ v₁ (λ _ → tt) (λ _ → tt) s≢z
    (subst (λ w → CmpL w t₁) (lvl-emb x (κ c₁)) (exact→cmp {ofU x} d ex))
```

## 结论 (按档)

- **[定理]** `posL`, `posX₁`, `X₁⊑U`, **`base⊏U`**, **`exact-keep-base`**, **`base⊏new`**, `newPos`, `ofU-mono`, **`cmp-new`** (构造); `Cnt`, `cnt⊑`, `cntC`, `notCntU`, **`U-not-cnt`**, `ofU-inj`, `ll⋢fin`, **`incomp-new`**, `incomp-new-od-ev`; `pt-up`, **`no-exact-up`**.
- **[判断]** 文件头的小结 (三种对的分类穷尽了上层折叠会遇到的比较: 判断, 依据种类与目标的分类; 若构造一路的目标类型另有形状, 要重看).
