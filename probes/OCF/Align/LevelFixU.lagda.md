# 唯一的定义域 $\mathbb U$, 与它上面的折叠

> 不含记号. 结论写在 [LevelFix](LevelFix.lagda.md). 块已经封闭, 所以块外可以写 $\mathbb U$: 下标是 $(k,c)$, `k` 是任何层号, `c : Raw k`. **这是一个 `Dom`, 一个定义域, 没有下标 $n$.** 同一个 `Lv`, `Fold`, 只实例化一次.

- 守卫 `⊑̂` 要求同层 (`gd`), 比较 `bd` 只比一个字面上界 $X$ 之下的两个第一位置 (`cmpD`). `≅ᴰ` 是 `≡`.
- `b₁`, `rd`: 这个定义域没有 `Ordᴵ` 的嵌入. `rd` 的字段由一个不合法的下界 `b₀` 空满足. 折叠不读这些字段 (读 [LevelFixTree](LevelFixTree.lagda.md)), 这里如实写明.
- `toU`, `fromU`: `LF` 与 `LG` 互相读. `Cf-toU`: 合法且名字满足 UIP 的层号读成好层号, 这就是折叠要的证书. **不需要逐层输入, 但 UIP 是条件 (§2).**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelFixU where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Free.Level using (Ordᴵ; _⊑ᴵ_; _≅ᴵ_)
open import OCF.Align.GuardTightLv using (Dom; module Lv)
open import OCF.Align.DomFoldDom using (module FlrOf)
open import OCF.Align.LevelFixCore
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelFixX using (XU)
```

## §1 $\mathbb U$

```agda
data Elt : Set where
  el : (j : LF) → Raw j → Elt

infix 4 _⊑̂_ _<̂_
data _⊑̂_ : Elt → Elt → Set where
  gd : ∀ {k c η} → Gd k c η → el k c ⊑̂ el k η

data _<̂_ : Elt → Elt → Set where
  lt : ∀ {k a X} → Dn k a X → Lgl k X → el k a <̂ el k X

ŝ : Elt → Elt
ŝ (el j c) = el j (G.suc c)

gs̃ : ∀ {c x y} → c ⊑̂ x → ŝ x ⊑̂ y → c ⊑̂ y
gs̃ {el k _} {el .k _} (gd (p , _)) (gd (q , l)) = gd (Cp-tr k p (inj₂ (Cp-suc k q)) , l)

s⊑̃ : ∀ {a b} → ŝ a ⊑̂ b → a ⊑̂ b
s⊑̃ {el k _} (gd (q , l)) = gd (inj₂ (Cp-suc k q) , l)

bd̃ : ∀ {a b X} → a <̂ X → b <̂ X → (a ⊑̂ b) ⊎ (b ⊑̂ a)
bd̃ {el k a} {el .k b} (lt {X = X} p w) (lt q _) with cmpD k X p q w
... | inj₁ c = inj₁ (gd (c , lgl-dn k X q w))
... | inj₂ c = inj₂ (gd (c , lgl-dn k X p w))

-- 不合法的下界: 第 0 步就不是第一位置
bogus : Raw zero
bogus = G.lim f where
  f : ℕ → Raw zero
  f zero = G.suc G.zero
  f (suc n) = G.zero

no-bogus : Lgl zero bogus → ⊥
no-bogus (st , w) with st 0
... | inj₁ ()
... | inj₂ ()

no-b₀ : ∀ {η} → el zero bogus ⊑̂ η → ⊥
no-b₀ (gd (p , l)) = no-bogus (lgl-cp zero p l)

𝕌 : Dom
𝕌 = record
  { D = Elt ; _⊑ᴰ_ = _⊑̂_ ; _≅ᴰ_ = _≡_ ; sD = ŝ
  ; ≅ᴰ-refl = λ x → refl ; ≅ᴰ-sym = sym ; ≅ᴰ-trans = trans
  ; conv = λ { refl e → e } ; gs = gs̃
  ; _<ᴰ_ = _<̂_ ; bd = bd̃ ; s⊑ᴰ = s⊑̃
  ; b₁ = el zero bogus
  ; rd = λ e → ⊥-elim (no-b₀ e)
  ; rd-one = λ e → ⊥-elim (no-b₀ e)
  ; rd-s = λ e e′ d → ⊥-elim (no-b₀ e)
  ; rd-≅ = λ e e′ d → ⊥-elim (no-b₀ e)
  ; rd-m = λ e e′ d → ⊥-elim (no-b₀ e)
  }

open Lv 𝕌 using (LG; _≈_; _⊴_; WFˢ; Cfˢ; Cpᶠ; ≈→⊴; ⊴-suc-r; ⊴-lim-r; ⊴-fst; z≈; s≈; l≈; o≈)
module U = Lv 𝕌
```

## §2 读来读去

```agda
toU : LF → LG
toUg : ∀ k c (g : (η : Raw k) → Gd k c η → LF) (x : Elt) → el k c ⊑̂ x → LG

toU zero = U.zero
toU (suc k) = U.suc (toU k)
toU (lim f) = U.lim (λ n → toU (f n))
toU (lc k c t g) = U.lc (el k c) (toU t) (toUg k c g)

toUg k c g (el .k η) (gd e) = toU (g η e)

fromU : LG → LF
fromU U.zero = zero
fromU (U.suc a) = suc (fromU a)
fromU (U.lim f) = lim (λ n → fromU (f n))
fromU (U.lc (el k c) t g) = lc k c (fromU t) (λ η e → fromU (g (el k η) (gd e)))

CP→Cpᶠ : ∀ {a b} → CP a b → Cpᶠ (toU a) (toU b)
CP→Cpᶠ self = U.self
CP→Cpᶠ (suc p) = U.suc (CP→Cpᶠ p)
CP→Cpᶠ (lim n p) = U.lim n (CP→Cpᶠ p)
CP→Cpᶠ (fst p) = U.fst (CP→Cpᶠ p)
```

**`cp⊴`: 字面的第一位置推出带转移的 `⊴`.** 这对任何 `Dom` 成立: 第一位置没有分支, 所以搬运对一切表成立. 这是 `fg→⊴` 的同类, 所以 `no-WFˢ-Ω⁺` 不碰 (它的反例要穿过分支).

```agda
cp⊴ : ∀ {a b} → b ≈ b → Cpᶠ a b → a ⊴ b
cp⊴ sf U.self = ≈→⊴ sf
cp⊴ (s≈ e) (U.suc p) = ⊴-suc-r (cp⊴ e p)
cp⊴ (l≈ h) (U.lim n p) = ⊴-lim-r n (cp⊴ (h n) p)
cp⊴ (o≈ d e h) (U.fst p) = ⊴-fst (cp⊴ e p)

```

**名字上的回路: 这是第一个障碍的编译事实.** 同一个下标过两个守卫证据时 (`≈`, `dir` 都要), 要从 `el k c ⊑̂ el k a` 反演出 `Gd k c a`. Agda 拒绝:

```text
h (el .k η) (gd e) .(el k η) (gd e′) refl
error: [SplitError.UnificationStuck]
  el k η ≟ el k η₁
  Cannot eliminate reflexive equation k = k of type LF because K has been disabled.
```

这不是检查器的保守: 反演要 `k ≡ k` 的回路是 `refl`, 也就是 `LF` 在 `k` 处满足 UIP. `LF` 里有函数, 没有函数外延证不出 (判断). 所以这里**把它写成条件 `Un x`**: `x` 里每个节点的名字满足 UIP. `Un` 对自然数名字是定理 (`uip-nat`, 编码-解码, 无假设), 所以 $\Omega_n$, $\Omega_\omega$ 无条件.

```agda
UIPk : LF → Set
UIPk k = ∀ (q : k ≡ k) → q ≡ refl

nmE : Elt → LF
nmE (el j _) = j

vl : ∀ {k} (x : Elt) → nmE x ≡ k → Raw k
vl (el j a) refl = a

vl-eq : ∀ {k a} → UIPk k → ∀ x (r : el k a ≡ x) (q : nmE x ≡ k) → vl x q ≡ a
vl-eq U .(el _ _) refl q rewrite U q = refl

el-inj : ∀ {k a b} → UIPk k → el k a ≡ el k b → a ≡ b
el-inj {k} {a} {b} U r = sym (vl-eq U (el k b) r refl)

module Inv {k : LF} {c : Raw k} (U : UIPk k) (g : (η : Raw k) → Gd k c η → LF) {a : Raw k} where
  go : ∀ z (e′ : el k c ⊑̂ z) → z ≡ el k a → Σ (Gd k c a) λ e₀ → toUg k c g z e′ ≡ toU (g a e₀)
  go .(el k _) (gd e₁) r with el-inj U r
  ... | refl = e₁ , refl

  inv : (e : el k c ⊑̂ el k a) → Σ (Gd k c a) λ e₀ → toUg k c g (el k a) e ≡ toU (g a e₀)
  inv e = go (el k a) e refl

Un : LF → Set
Un zero = ⊤
Un (suc k) = Un k
Un (lim f) = ∀ n → Un (f n)
Un (lc k c t g) = UIPk k × Un t × (∀ η e → Un (g η e))

self-U : ∀ x → Legal x → Un x → toU x ≈ toU x
self-U zero w u = z≈
self-U (suc k) w u = s≈ (self-U k w u)
self-U (lim f) (st , w) u = l≈ (λ n → self-U (f n) (w n) (u n))
self-U (lc k c t g) (_ , _ , _ , irr , wt , wg) (uk , ut , ug) = o≈ refl (self-U t wt ut) h
  where
  h : ∀ (η : Elt) (e : el k c ⊑̂ η) (η′ : Elt) (e′ : el k c ⊑̂ η′) → η ≡ η′ → toUg k c g η e ≈ toUg k c g η′ e′
  h (el .k a) (gd e) .(el k a) e′ refl with Inv.inv uk g e′
  ... | e₀ , eq = subst (λ z → toU (g a e) ≈ z) (sym eq)
      (subst (λ z → toU (g a e) ≈ toU z) (irr a e e₀) (self-U (g a e) (wg a e) (ug a e)))

WF-U : ∀ x → Legal x → Un x → WFˢ (toU x)
WF-U zero w u = tt
WF-U (suc k) w u = WF-U k w u
WF-U (lim f) (st , w) u =
  (λ n → cp⊴ (self-U (f (suc n)) (w (suc n)) (u (suc n))) (CP→Cpᶠ (st n))) , (λ n → WF-U (f n) (w n) (u n))
WF-U (lc k c t g) (_ , tg , dir , irr , wt , wg) (uk , ut , ug) =
  tg′ , dir′ , WF-U t wt ut , wg′
  where
  tg′ : ∀ (η : Elt) (e : el k c ⊑̂ η) → toU t ⊴ toUg k c g η e
  tg′ (el .k η) (gd e) = cp⊴ (self-U (g η e) (wg η e) (ug η e)) (CP→Cpᶠ (tg η e))
  dir′ : ∀ (η : Elt) (e : el k c ⊑̂ η) (η′ : Elt) (e′ : el k c ⊑̂ η′) → η ⊑̂ η′ → toUg k c g η e ⊴ toUg k c g η′ e′
  dir′ (el .k a) (gd e) (el .k a′) e′ (gd d) with Inv.inv uk g e′
  ... | e₀ , eq = subst (λ z → toU (g a e) ⊴ z) (sym eq)
      (cp⊴ (self-U (g a′ e₀) (wg a′ e₀) (ug a′ e₀)) (CP→Cpᶠ (dir a e a′ e₀ d)))
  wg′ : ∀ (η : Elt) (e : el k c ⊑̂ η) → WFˢ (toUg k c g η e)
  wg′ (el .k η) (gd e) = WF-U (g η e) (wg η e) (ug η e)

Cf-toU : ∀ x → Legal x → Un x → Cfˢ (toU x)
Cf-toU x w u = WF-U x w u , self-U x w u
```

## §3 求界: 字面上界之下取最大

地板的项都在同一层 (`lt` 的索引). 局部上界是分支的后继. 没有比较两个分支路径.

```agda
private
  module F = FlrOf 𝕌

record MaxR (k : LF) (Y : Raw k) (φ : F.Flr) (m : Raw k) : Set where
  constructor mxr
  field
    M   : Raw k
    M<  : Dn k M Y
    m⊑  : Cp k m M
    all : ∀ {K} → F.InF K φ → K ⊑̂ el k M

maxF : ∀ {k Y} (φ : F.Flr) → F.Ev (el k Y) φ → ∀ m → Dn k m Y → Lgl k Y → MaxR k Y φ m
maxF {k} {Y} F.fz e m q w = mxr m q (inj₁ refl) (λ ())
maxF {k} {Y} (F.fk K) (lt {a = a} p _) m q w with cmpD k Y q p w
... | inj₁ c = mxr a p c (λ { F.ink → gd (inj₁ refl , lgl-dn k Y p w) })
... | inj₂ c = mxr m q (inj₁ refl) (λ { F.ink → gd (c , lgl-dn k Y q w) })
maxF {k} {Y} (a F.⊔ b) (x , y) m q w with maxF a x m q w
... | mxr M₁ M₁< m₁ al₁ with maxF b y M₁ M₁< w
...   | mxr M₂ M₂< m₂ al₂ = mxr M₂ M₂< (Cp-tr k m₁ m₂) all′
  where
  all′ : ∀ {K} → F.InF K (a F.⊔ b) → K ⊑̂ el k M₂
  all′ (F.inl i) with al₁ i
  ... | gd (p , _) = gd (Cp-tr k p m₂ , lgl-dn k Y M₂< w)
  all′ (F.inr i) = al₂ i

evsuc : ∀ {k x} (φ : F.Flr) → Lgl k x → (∀ {K} → F.InF K φ → K ⊑̂ el k x) → F.Ev (el k (G.suc x)) φ
evsuc F.fz l h = tt
evsuc {k} {x} (F.fk K) l h with h F.ink
... | gd (p , _) = lt p l
evsuc (a F.⊔ b) l h = evsuc a l (λ i → h (F.inl i)) , evsuc b l (λ i → h (F.inr i))

boundU : ∀ {ℓ K₀} (φ : F.Flr) → F.Ev ℓ φ → K₀ <̂ ℓ → F.Tp ℓ φ
boundU {el k Y} φ y (lt {a = m} q w) with maxF φ y m q w
... | mxr M M< m⊑ all = F.tpr (el k M) all upX′ upEv′ up<′
  where
  upX′ : ∀ {η} → el k M ⊑̂ η → Elt
  upX′ {η} d = ŝ η
  upEv′ : ∀ {η} (d : el k M ⊑̂ η) → F.Ev (ŝ η) φ
  upEv′ (gd (p , l)) = evsuc φ l (λ i → up⊑ (all i) p l)
    where
    up⊑ : ∀ {K x} → K ⊑̂ el k M → Cp k M x → Lgl k x → K ⊑̂ el k x
    up⊑ (gd (r , _)) p′ l′ = gd (Cp-tr k r p′ , l′)
  up<′ : ∀ {η} (d : el k M ⊑̂ η) → η <̂ ŝ η
  up<′ (gd (p , l)) = lt (inj₁ refl) l
```

## §4 实例

`ix`: 节点的层是自然数就是这个数; 否则是 0, 这时闭包不带链 (见 [LevelFix](LevelFix.lagda.md) "第一个障碍"). `nodeC n`, `nodeF n` 就是 $\Omega_n$, 对一切 $n$ 一个定义, 没有 "高于塔的哑值".

```agda
natOfL : LF → ℕ
natOfL zero = 0
natOfL (suc a) = suc (natOfL a)
natOfL (lim _) = 0
natOfL (lc _ _ _ _) = 0

XF : XU
XF = record
  { 𝔻 = 𝕌
  ; ⊑-tr = λ { (gd (p , _)) (gd (q , l)) → gd (Cp-tr _ p q , l) }
  ; self<G = λ { (gd (p , l)) → lt (inj₁ refl) l }
  ; bound = boundU
  ; ix = λ { (el j _) → natOfL j }
  ; nodeC = λ n → el (natF n) (cO (natF n))
  ; nodeF = λ n → toU (Ω̂ (natF n))
  ; emᵈ = λ { (el j c) → toU (up j c) }
  ; bot = el zero G.zero
  }
```

## §5 自然数名字的 UIP

编码-解码. `code n y`: $y$ 就是字面的 `natF n`. 它是命题 (`⊤` 或 `⊥`), 所以 `natF n` 处的回路都是 `refl`. 没有假设.

```agda
code : ℕ → LF → Set
code zero zero = ⊤
code zero (suc _) = ⊥
code zero (lim _) = ⊥
code zero (lc _ _ _ _) = ⊥
code (suc n) zero = ⊥
code (suc n) (suc y) = code n y
code (suc n) (lim _) = ⊥
code (suc n) (lc _ _ _ _) = ⊥

enc₀ : ∀ n → code n (natF n)
enc₀ zero = tt
enc₀ (suc n) = enc₀ n

enc : ∀ n {y} → natF n ≡ y → code n y
enc n refl = enc₀ n

dec : ∀ n y → code n y → natF n ≡ y
dec zero zero c = refl
dec (suc n) (suc y) c = cong suc (dec n y c)

code-prop : ∀ n y (a b : code n y) → a ≡ b
code-prop zero zero tt tt = refl
code-prop (suc n) (suc y) a b = code-prop n y a b

dec-enc₀ : ∀ n → dec n (natF n) (enc₀ n) ≡ refl
dec-enc₀ zero = refl
dec-enc₀ (suc n) = cong (cong suc) (dec-enc₀ n)

dec-enc : ∀ n {y} (p : natF n ≡ y) → dec n y (enc n p) ≡ p
dec-enc n refl = dec-enc₀ n

uip-nat : ∀ n → UIPk (natF n)
uip-nat n q = trans (sym (dec-enc n q))
  (trans (cong (dec n (natF n)) (code-prop n (natF n) (enc n q) (enc n refl))) (dec-enc n refl))

Un-up : ∀ n T → Un (up (natF n) T)
Un-T : ∀ n → Un (upT (natF n))
Un-N : ∀ n r c t (g : (η : Low (natF n) r) → GdL (natF n) r c η → LF) → Un t → (∀ η e → Un (g η e)) → Un (upN (natF n) r c t g)

Un-N (suc n) (inj₁ _) c t g ut ug = uip-nat n , ut , ug
Un-N (suc n) (inj₂ r) c t g ut ug = Un-N n r c t g ut ug

Un-up n G.zero = tt
Un-up n (G.suc a) = Un-up n a
Un-up n (G.lim f) = λ m → Un-up n (f m)
Un-up n (G.lc r c t g) = Un-N n r c _ _ (Un-up n t) (λ η e → Un-up n (g η e))
Un-up (suc n) (G.em _ T) = Un-up n T
Un-up n G.top = Un-T n

Un-T zero = tt
Un-T (suc n) = uip-nat n , Un-T n , (λ η e → Un-up n η)

Un-Ωω : Un Ωω
Un-Ωω = λ n → Un-T n

Un-add : ∀ x a → Un x → Un a → Un (x +ᴸ a)
Un-add x zero u v = u
Un-add x (suc a) u v = Un-add x a u v
Un-add x (lim f) u v = λ n → Un-add x (f n) u (v n)
Un-add x (lc k c t g) u (uk , ut , ug) = uk , Un-add x t u ut , (λ η e → Un-add x (g η e) u (ug η e))
```
