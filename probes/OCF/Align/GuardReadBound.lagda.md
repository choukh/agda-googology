# 统一读法的界: 紧, 最小, 不看穿过的分支

> 不含记号. 结论写在 [GuardRead](GuardRead.lagda.md). [GuardTightBound](GuardTightBound.lagda.md) 的 `tail-ub`, `tail-lb`, `tail-free`, `nf-tail` 只对 $a+\eta$. 这里对**任何**带 `Reader` 的闭包, 所以对 $F\,\theta$ 里的每个闭包与 $\mathrm{Lv}_5$.
>
> - §1 `tgt-of`, `lc-of`: 后继与闭包节点的回答只有两种, 第一支或 "$G\,b$ 在节点之下的分支 $b+1$". `tight-min`: **这个分支是最小的**: $G\,b\trianglelefteq k$ 且 $G\,x\trianglelefteq G\,b$ 时 $k$ 不在 $G\,x$ 之下. 由良基 (`irr`), 不判定.
> - §2 `no-occ`: 闭包的分支里没有 $\approx$ 它自己的闭包. 所以路径内部不贡献同键的地板. 这取代 `tail-ub` 里 "路径内部没有 `bra`".
> - §3 `bra-ub`, `bra-lb`, `bra-free`, `fst-ub`: 目标 `suc (bra (b+1) ea r)`, $r$ 任意: 界模前序就是 $b+1$. 目标在第一支: 界模前序就是下界 $c$.
> - §4 `nf-rdB`, `nf-rdF`, `tight-nf`: 目标 `suc (bra τ e r)` 规范化之后是 `suc (bra (b+1) …)`, $G\,b\trianglelefteq$ 目标, 或 `suc (fst …)`. **$\tau$ 只经读法进来.** `ans-≅`: 同一个世界里同一个目标的回答相同. `bound-of`: 合起来的界.
> - §5 `tight-Lv₅`, `tight-F₁`, `tight-of`, `bound-Lv₅`, `bound-F₁`, `free-Lv₅`, `free-bound`: 实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardReadBound where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.GuardTightCum using (Ordᴵ; <ᴵ-dec; _<ᴵ_; _⊑ᴵ_; _≺ᴵ_; _≅ᴵ_; via; zero; suc; lim; z≅; s⊑; z⊑; ≅ᴵ-refl; ⊑ᴵ-refl; ⊑ᴵ-trans; Ordᶜ)
open import OCF.Free.Floor using (InF; ink; inb; inl; inr)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; toCp; irr)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree using (module Fold)
open import OCF.Align.GuardTightBound using (module Land)
import OCF.Align.GuardTightUni as Uni
private module Un = Uni Dom₀
open Un using (F; F-mono; Lv₅; rb₁; ψ¹; em; em-mono)
open import OCF.Align.GuardReadCut using (Ab; LZ)
open import OCF.Align.GuardReadRd
```

## §1 回答的规格, 最小

```agda
pth→st : ∀ {k c} → k < c → Strict k c
pth→st zero        = st-suc self
pth→st (suc r)     = st-suc (toCp r)
pth→st (lim n r)   = st-lim n (toCp r)
pth→st (fst r)     = st-fst (toCp r)
pth→st (bra η e r) = st-bra η e (toCp r)

-- 定理: G b ⊴ k, G x ⊴ G b, 则 k 不在 G x 之下
tight-min : ∀ {A B k} → B ⊴ k → A ⊴ B → Below k A → ⊥
tight-min {k = k} bk ab (pre d r) with ⊴p (⊴-trans ab bk) r
... | viaᴸ d′ p _ = irr k (pth→st p) (≈-trans d d′)

-- 同一件事, 目标模 Lk
tight-min′ : ∀ {A B k y} → B ⊴ k → A ⊴ B → Lk k y → y < A → ⊥
tight-min′ {k = k} bk ab (inj₁ d) r with ⊴p (⊴-trans ab bk) r
... | viaᴸ d′ p _ = irr k (pth→st p) (≈-trans d d′)
tight-min′ {k = k} bk ab (inj₂ refl) r with ⊴p (⊴-trans ab bk) r
... | viaᴸ d′ p _ = irr k (pth→st p) d′

module Spec (G : Ordᴵ → LG) (g01 : G zero ⊴ G (suc zero))
            (str : ∀ b → NZ b → ∀ {k} (P : Cp k (G (suc b))) → OCF.Align.GuardReadCut.Cu (G b) P)
            (cnt : ∀ f s → G (lim f s) ≈ lim (λ n → G (f n))) where
  open Reader G g01 str cnt

  -- 目标 (位置 suc k′) 的回答
  data IsT {η₀ x k′} {P : Cp (suc k′) x} : Rx η₀ P → Set where
    isF : ∀ {rep} (d : Lk (suc k′) rep) Q u → IsT (xF d Q u)
    isN : ∀ {rep} b nz ea m (d : Lk (suc k′) rep) Q u w → G b ⊴ k′ → IsT (xN b nz ea m d Q u w)

  tgt-of : ∀ {η₀ x k′} {P : Cp (suc k′) x} (r : Rx η₀ P) → IsT r
  tgt-of (xF d Q u) = isF d Q u
  tgt-of (xN b nz ea m d Q u (inj₁ w)) = isN b nz ea m d Q u (inj₁ w) (lower d w)
    where
    lower : ∀ {k′ rep A} → Lk (suc k′) rep → Ab A rep → A ⊴ k′
    lower (inj₁ (s≈ e)) w = ⊴-trans w (≈→⊴ (≈-sym e))
    lower (inj₂ refl) w = w
  tgt-of (xN b nz ea m d Q u (inj₂ z)) = ⊥-elim (lz-lk d z)
  tgt-of (xL a ea m Q u ())
  tgt-of (xC ())

  -- 闭包节点的回答
  data IsC {η₀ x c t g} {P : Cp (lc c t g) x} : Rx η₀ P → Set where
    icF : ∀ {rep} (d : Lk (lc c t g) rep) Q u → IsC (xF d Q u)
    icN : ∀ {rep} b nz ea m (d : Lk (lc c t g) rep) Q u w → G b ⊴ lc c t g → IsC (xN b nz ea m d Q u w)

  lc-of : ∀ {η₀ x c t g} {P : Cp (lc c t g) x} (r : Rx η₀ P) → IsC r
  lc-of (xF d Q u) = icF d Q u
  lc-of (xN b nz ea m d Q u (inj₁ w)) = icN b nz ea m d Q u (inj₁ w) (lower d w)
    where
    lower : ∀ {c t g rep A} → Lk (lc c t g) rep → Ab A rep → A ⊴ lc c t g
    lower {rep = lc _ _ _} (inj₁ e) w = ⊴-trans w (≈→⊴ (≈-sym e))
    lower (inj₂ refl) w = w
  lc-of (xN b nz ea m d Q u (inj₂ z)) = ⊥-elim (lz-lk d z)
  lc-of (xL a ea m Q u ())
  lc-of (xC ())
```

## §2 分支里没有自己

```agda
module NoOcc (c : LG) (wf : WFˢ c) (sf : c ≈ c) (tc : Tc c) where
  open Land c wf sf tc

  occ-pos : ∀ {y K x a} {r : x < a} → OccA y K r → Σ Ordᴵ λ c₃ → Σ LG λ t₃ → Σ ((η : Ordᴵ) → c₃ ⊑ᴵ η → LG) λ g₃ → Cp (lc c₃ t₃ g₃) a × (lc c₃ t₃ g₃ ≈ y)
  occ-pos (oh {c₃ = c₃} {t₃ = t₃} {g₃ = g₃} η e r d _) = c₃ , t₃ , g₃ , self , d
  occ-pos (ob η e o) with occ-pos o
  ... | c₃ , t₃ , g₃ , P , d = c₃ , t₃ , g₃ , bra η e P , d
  occ-pos (os′ o) with occ-pos o
  ... | c₃ , t₃ , g₃ , P , d = c₃ , t₃ , g₃ , suc P , d
  occ-pos (ol′ n o) with occ-pos o
  ... | c₃ , t₃ , g₃ , P , d = c₃ , t₃ , g₃ , lim n P , d
  occ-pos (of′ o) with occ-pos o
  ... | c₃ , t₃ , g₃ , P , d = c₃ , t₃ , g₃ , fst P , d

  no-occ-b : ∀ {c₁ t₁ g₁ K x} η e {r : x < g₁ η e} → OccA (lc c₁ t₁ g₁) K r → ⊥
  no-occ-b {c₁} {t₁} {g₁} η e o with occ-pos o
  ... | c₃ , t₃ , g₃ , P , d = irr (lc c₁ t₁ g₁) (st-bra η e P) (≈-sym d)

  no-occ-f : ∀ {c₁ t₁ g₁ K x} {r : x < t₁} → OccA (lc c₁ t₁ g₁) K r → ⊥
  no-occ-f {c₁} {t₁} {g₁} o with occ-pos o
  ... | c₃ , t₃ , g₃ , P , d = irr (lc c₁ t₁ g₁) (st-fst P) (≈-sym d)
```

## §3 界: 对任意闭包, 任意路径内部

```agda
module BdU {c₁ : Ordᴵ} {t₁ : LG} {g₁ : (η : Ordᴵ) → c₁ ⊑ᴵ η → LG} (w₀ : WFˢ (lc c₁ t₁ g₁)) (s₀ : lc c₁ t₁ g₁ ≈ lc c₁ t₁ g₁) (tc : Tc (lc c₁ t₁ g₁)) where
  L : LG
  L = lc c₁ t₁ g₁
  open Land (suc L) w₀ (s≈ s₀) tc
  open Fold (suc L) w₀ (s≈ s₀) tc
  open NoOcc (suc L) w₀ (s≈ s₀) tc

  st₀ : ∀ {E ρ} → St E ρ tz
  st₀ ()

  module Br {b x} (ea : c₁ ⊑ᴵ suc b) (r : x < g₁ (suc b) ea) (E : Ents) (aq : Adm (tab E) (suc (bra (suc b) ea r))) where
    SS₀ = SSc {ρ = tz} E (tp (suc (bra (suc b) ea r)) aq) (st₀ {E}) (suc self) tt
    w = Sel.wit SS₀

    only-b : ∀ {K} → InF K (Sel.φ SS₀) → K ≡ b
    only-b i with floors E (tp (suc (bra (suc b) ea r)) aq) (st₀ {E}) (suc self) tt i
    ... | fromSt (Occ.sfr () _ _)
    ... | fromSt (Occ.spf _ () _)
    ... | fromTgt refl (os′ (oh _ _ _ _ refl)) = refl
    ... | fromTgt refl (os′ (ob _ _ o)) = ⊥-elim (no-occ-b _ _ o)
    ... | fromPos (os′ ())

    in-b : InF b (Sel.φ SS₀)
    in-b = inr (inl (inl ink))

    bra-ub : cOf w ⊑ᴵ suc b
    bra-ub = cOf-ub w ea (λ i → sub (only-b i))
      where
      sub : ∀ {K} → K ≡ b → K ≺ᴵ suc b
      sub refl = via (≅ᴵ-refl b) zero

    bra-lb : suc b ⊑ᴵ cOf w
    bra-lb with cOf-lb₂ w in-b refl
    ... | via d r′ = s⊑ d r′

  -- 界不看世界, 不看路径内部
  bra-free : ∀ {b x x′} (ea ea′ : c₁ ⊑ᴵ suc b) (r : x < g₁ (suc b) ea) (r′ : x′ < g₁ (suc b) ea′) (E E′ : Ents)
             (aq : Adm (tab E) (suc (bra (suc b) ea r))) (aq′ : Adm (tab E′) (suc (bra (suc b) ea′ r′))) →
             cOf (Br.w ea r E aq) ⊑ᴵ cOf (Br.w ea′ r′ E′ aq′)
  bra-free ea ea′ r r′ E E′ aq aq′ = ⊑ᴵ-trans (Br.bra-ub ea r E aq) (Br.bra-lb ea′ r′ E′ aq′)

  pthF : ∀ {x} → x < t₁ → x < suc L
  pthF r = suc (fst r)

  module Fr {x} (r : x < t₁) (E : Ents) (aq : Adm (tab E) (pthF r)) where
    SS₀ = SSc {ρ = tz} E (tp (pthF r) aq) (st₀ {E}) (suc self) tt
    w = Sel.wit SS₀

    none : ∀ {K} → InF K (Sel.φ SS₀) → ⊥
    none i with floors E (tp (pthF r) aq) (st₀ {E}) (suc self) tt i
    ... | fromSt (Occ.sfr () _ _)
    ... | fromSt (Occ.spf _ () _)
    ... | fromTgt refl (os′ (of′ o)) = no-occ-f o
    ... | fromPos (os′ ())

    fst-ub : cOf w ⊑ᴵ c₁
    fst-ub = cOf-ub w ⊑ᴵ-refl (λ i → ⊥-elim (none i))

    fst-lb : c₁ ⊑ᴵ cOf w
    fst-lb = cOf-lb₁ w
```

## §4 规范化

`nf-rdB`, `nf-rdF`: 对任何读法: 读位置回答什么分支, 规范化的目标就走那个分支. `tight-nf`: 对 `Reader`.

```agda
nf-rdB : ∀ {c t g} (tc : Tc (lc c t g)) η e {x} (r : x < g η e) {rep} a ea l (d : Lk (suc x) rep) (Q : Cp rep (g a ea)) tr →
         proj₁ tc η e (toCpS r) ≡ rdB a ea l d Q tr →
         Σ _ λ r′ → pathT (nfT (suc (lc _ t g)) tc (suc (bra η e r))) ≡ suc (bra a ea r′)
nf-rdB {g = g} (rd , tt′ , tg) η e r a ea l d Q tr eq rewrite eq with nfC (g a ea) (tg a ea) Q
... | nfc d′ Q′ u r′ with lkC d d′
... | inj₁ (s≈ _) = _ , refl
... | inj₂ refl = _ , refl

nf-rdF : ∀ {c t g} (tc : Tc (lc c t g)) η e {x} (r : x < g η e) {rep} (d : Lk (suc x) rep) (Q : Cp rep t) tr →
         proj₁ tc η e (toCpS r) ≡ rdF d Q tr →
         Σ _ λ r′ → pathT (nfT (suc (lc _ t g)) tc (suc (bra η e r))) ≡ suc (fst r′)
nf-rdF {t = t} (rd , tt′ , tg) η e r d Q tr eq rewrite eq with nfC t tt′ Q
... | nfc d′ Q′ u r′ with lkC d d′
... | inj₁ (s≈ _) = _ , refl
... | inj₂ refl = _ , refl

LG₁ : (Ordᴵ → LG) → LG
LG₁ G = lc (suc zero) (G (suc zero)) (λ η e → G η)

-- 目标规范化之后的形状
NfShape : (G : Ordᴵ → LG) (tc : Tc (LG₁ G)) → ∀ τ (e : suc zero ⊑ᴵ τ) {x} (r : x < G τ) → Set
NfShape G tc τ e {x} r =
  (Σ _ λ r′ → pathT (nfT (suc (LG₁ G)) tc (suc (bra τ e r))) ≡ suc (fst r′))
  ⊎ (Σ Ordᴵ λ b → NZ b × (G b ⊴ x) × (Σ LG λ y → Lk x y × (y < G (suc b))) ×
       (Σ (suc zero ⊑ᴵ suc b) λ ea → Σ _ λ r′ → pathT (nfT (suc (LG₁ G)) tc (suc (bra τ e r))) ≡ suc (bra (suc b) ea r′)))

ext : ∀ {x rep A} → Lk (suc x) rep → Cp rep A → Σ LG λ y → Lk x y × (y < A)
ext (inj₁ (s≈ d)) Q = _ , inj₁ d , fromCpS Q
ext (inj₂ refl) Q = _ , inj₂ refl , fromCpS Q

module TightT (G : Ordᴵ → LG) (g01 : G zero ⊴ G (suc zero))
              (str : ∀ b → NZ b → ∀ {k} (P : Cp k (G (suc b))) → OCF.Align.GuardReadCut.Cu (G b) P)
              (cnt : ∀ f s → G (lim f s) ≈ lim (λ n → G (f n)))
              (tct : Tc (G (suc zero))) (tcg : ∀ η → Tc (G η)) where
  open Reader G g01 str cnt
  open Spec G g01 str cnt

  tcL : Tc (LG₁ G)
  tcL = rdU , tct , (λ η e → tcg η)

  tight-nf : ∀ τ e {x} (r : x < G τ) → NfShape G tcL τ e r
  tight-nf τ e r = help (rx τ e (toCpS r)) refl (tgt-of (rx τ e (toCpS r)))
    where
    help : (w : Rx τ (toCpS r)) → rx τ e (toCpS r) ≡ w → IsT w → NfShape G tcL τ e r
    help (xF d Q u) eq (isF _ _ _) = inj₁ (nf-rdF tcL τ e r d Q u (cong (toRd {τ} {e}) eq))
    help (xN b nz ea m d Q u w) eq (isN _ _ _ _ _ _ _ _ low) = inj₂ (b , nz , low , ext d Q , ea , nf-rdB tcL τ e r (suc b) ea m d Q u (cong (toRd {τ} {e}) eq))

-- 定理: 同一个世界里 (b, b′ 有字面的公共上界), 同一个目标的两个回答给同一个分支
ans-≅ : ∀ {G : Ordᴵ → LG} (mono : ∀ {a b} → a ⊑ᴵ b → G a ⊴ G b) {b b′ x x′ y y′ X} →
        Lk x x′ → G b ⊴ x → G b′ ⊴ x′ → Lk x y → y < G (suc b) → Lk x′ y′ → y′ < G (suc b′) → b <ᴵ X → b′ <ᴵ X → b ≅ᴵ b′
ans-≅ mono d low low′ ly ry ly′ ry′ p q with <ᴵ-dec p q
... | injᵃ (via e r) = ⊥-elim (tight-min′ (lkB d low′) (mono (s⊑ e r)) ly ry)
  where
  lkB : ∀ {A x x′} → Lk x x′ → A ⊴ x′ → A ⊴ x
  lkB (inj₁ e′) a = ⊴-trans a (≈→⊴ (≈-sym e′))
  lkB (inj₂ refl) a = a
... | injᵇ (via e r) = ⊥-elim (tight-min′ (lkF d low) (mono (s⊑ e r)) ly′ ry′)
  where
  lkF : ∀ {A x x′} → Lk x x′ → A ⊴ x → A ⊴ x′
  lkF (inj₁ e′) a = ⊴-trans a (≈→⊴ e′)
  lkF (inj₂ refl) a = a
... | injᶜ c = c

module Full (G : Ordᴵ → LG) (tc : Tc (LG₁ G)) (w₀ : WFˢ (LG₁ G)) (s₀ : LG₁ G ≈ LG₁ G) where
  open BdU {suc zero} {G (suc zero)} {λ η e → G η} w₀ s₀ tc
  open Fold (suc (LG₁ G)) w₀ (s≈ s₀) tc

  -- 目标 q 之下, 第一个闭包位置的界
  cOfQ : ∀ {k} (q : k < suc (LG₁ G)) (E : Ents) → Adm (tab E) q → Ordᴵ
  cOfQ q E aq = cOf (Sel.wit (SSc {ρ = tz} E (tp q aq) (st₀ {E}) (suc self) tt))

  private
    hF : ∀ {k} (q : k < suc (LG₁ G)) (r′ : k < G (suc zero)) E (aq : Adm (tab E) q) → q ≡ suc (fst r′) → (cOfQ q E aq ⊑ᴵ suc zero) × (suc zero ⊑ᴵ cOfQ q E aq)
    hF _ r′ E aq refl = Fr.fst-ub r′ E aq , Fr.fst-lb r′ E aq

    hB : ∀ {k b} (q : k < suc (LG₁ G)) (ea : suc zero ⊑ᴵ suc b) (r′ : k < G (suc b)) E (aq : Adm (tab E) q) → q ≡ suc (bra (suc b) ea r′) → (cOfQ q E aq ⊑ᴵ suc b) × (suc b ⊑ᴵ cOfQ q E aq)
    hB _ ea r′ E aq refl = Br.bra-ub ea r′ E aq , Br.bra-lb ea r′ E aq

  -- 定理: 规范化之后的界. 对一切 τ, 一切路径, 一切世界.
  bound-of : ∀ τ e {x} (r : x < G τ) → NfShape G tc τ e r → ∀ E (aq : Adm (tab E) (pathT (nfT (suc (LG₁ G)) tc (suc (bra τ e r))))) →
             ((cOfQ _ E aq ⊑ᴵ suc zero) × (suc zero ⊑ᴵ cOfQ _ E aq))
             ⊎ (Σ Ordᴵ λ b → (G b ⊴ x) × (cOfQ _ E aq ⊑ᴵ suc b) × (suc b ⊑ᴵ cOfQ _ E aq))
  bound-of τ e r (inj₁ (r′ , eq)) E aq = inj₁ (hF _ r′ E aq eq)
  bound-of τ e r (inj₂ (b , nz , low , _ , ea , r′ , eq)) E aq = inj₂ (b , low , hB _ ea r′ E aq eq)
```

## §5 实例: 第 5 站, $\psi_1(\Omega)$

对一切 $\tau$, 一切路径 $r$. `min-Lv₅`: 分支 $b+1$ 是最小的. **这是 `c-bra*` 那一半在第 5 站上的否定: 上界不再读到穿过的 $\tau$, 对一切 $\tau$, 编译.** 界的数值是 `bra-ub`, `bra-lb`.

```agda
open import OCF.Align.GuardReadCut using (read; Sp)
open Un using (b1; idO; em-self; Good; gi; rb-≈₁₁; _⊑ᵒ_; good-F)
open import OCF.Align.GuardReadRs using (Rs; ri; Rs-ψ¹; Rs-Ω; Rd)
open import OCF.Align.GuardTightCum using (limᵢ; _≅_; Ω-refl)

module Lv₅T = TightT F (F-mono z⊑) (λ b nz P → read b1 b1 (sp-F b nz) P) (λ g s → l≈ (λ n → Un.self-F (g n))) (Tc-F (suc zero)) Tc-F

tight-Lv₅ = Lv₅T.tight-nf

min-Lv₅ : ∀ {b x k} → x ⊑ᴵ b → F b ⊴ k → Below k (F x) → ⊥
min-Lv₅ m bk bl = tight-min bk (F-mono m) bl

-- 任何带切口的闭包: Tc-of 给的读法就是 Reader, 所以同一个定理
tight-of : ∀ {f : Ordᶜ zero → Ordᶜ (suc zero)} (R : Rs (limᵢ zero f)) (g : Good (limᵢ zero f)) →
           ∀ τ e {x} (r : x < rb₁ (f (em τ))) → NfShape (λ η → rb₁ (f (em η))) (Tc-of R g) τ e r
tight-of {f} (ri hb st ct) (gi hb′ hm) =
  TightT.tight-nf (λ η → rb₁ (f (em η))) (hm (em-mono z⊑) (idO {b = b1} {b′ = b1}))
    (λ b nz P → read b1 b1 (st (em b) (em-self b)) P)
    (λ g s → rb-≈₁₁ (ct (λ n → em (g n)) (λ n → em-self (g n))))
    (Tc-of (hb (suc zero) (s≅′) (rs′)) (hb′ (suc zero) (s≅′) (gs′)))
    (λ η → Tc-of (hb (em η) (em-self η) (Rs-em′ η)) (hb′ (em η) (em-self η) (Un.good-em η)))
  where
  open import OCF.Align.GuardReadRs using (rs; rz) renaming (Rs-em to Rs-em′)
  open import OCF.Align.GuardTightCum using (s≅)
  s≅′ = s≅ z≅
  rs′ = rs rz
  gs′ = Un.gs Un.gz

-- ψ₁(Ω): L = F 1, 分支 ψ₁(τ)
tight-F₁ = tight-of (Rs-ψ¹ (Rs-Ω (suc zero)) (Ω-refl (suc zero))) (good-F (suc zero))
```

**第 5 站与 $\psi_1(\Omega)$ 的界.** `bound-Lv₅`, `bound-F₁`: 规范化之后, 目标 `x` 的界模前序是 1 (第一支) 或 $b+1$, $F\,b\trianglelefteq x$. `free-Lv₅`: 同一个世界里, 同一个目标 (不管穿过哪个分支 $\tau$) 给同一个 $b$. 公共上界由表给: 路径上的分支 $b+1$ 的证据就是 $b<\ell$, 同键同一个 $\ell$.

```agda
open Un using (Cf-Lv₅; Cf-F)

module Lv₅F = Full F Lv₅T.tcL (proj₁ Cf-Lv₅) (proj₂ Cf-Lv₅)

bound-Lv₅ : ∀ τ e {x} (r : x < F τ) → _
bound-Lv₅ τ e r = Lv₅F.bound-of τ e r (tight-Lv₅ τ e r)

free-Lv₅ : ∀ {b b′ x y y′ X} → F b ⊴ x → F b′ ⊴ x → Lk x y → y < F (suc b) → Lk x y′ → y′ < F (suc b′) → b <ᴵ X → b′ <ᴵ X → b ≅ᴵ b′
free-Lv₅ = ans-≅ F-mono (inj₂ refl)

module F₁F = Full (λ η → rb₁ (ψ¹ (em η))) (Tc-F (suc zero)) (proj₁ (Cf-F (suc zero))) (proj₂ (Cf-F (suc zero)))

bound-F₁ : ∀ τ e {x} (r : x < rb₁ (ψ¹ (em τ))) → _
bound-F₁ τ e r = F₁F.bound-of τ e r (tight-F₁ τ e r)

-- 两个目标同一个分支, 界互相 ⊑
free-bound : ∀ {b b′ c c′} → b ≅ᴵ b′ → c ⊑ᴵ suc b → suc b′ ⊑ᴵ c′ → c ⊑ᴵ c′
free-bound e ub lb = ⊑ᴵ-trans ub (⊑ᴵ-trans (s⊑ e zero) lb)
```
