# 层号参数化的无符号闭包定理 (六′): `Gᵀ` 沿层号搬运

> 接 [UniformNF5Good](UniformNF5Good.lagda.md), 形状照值层的 `Tr`/`Tr⁻`/`Bk`/`Bk⁻` ([UniformNF5Class](UniformNF5Class.lagda.md) §7). 结论先说:
>
> 1. **`Trᵀ`, `Tr⁻ᵀ`: `Gᵀ` 跨 $\cong^\mathsf I$ 不变.** 除 `gΩ` 外, 每一行都是 `Iota` 的逐字替换 (`ι q` 换成 `trO ε`, `pι` 换成 `ptr`), 由脚本从 `Iota` 生成. 对层号或树的形状没有新的分情况.
> 2. **`gΩ` 行要拉回.** 新节点的输入 $z$ 在代表元层, `backO` 把它送回原层. `bkC` 是上下文侧的对偶: $\mathtt{run}\,(\mathtt{bkC}\,D)\,u\equiv\mathtt{run}\,D\,(\mathtt{backO}\,u)$ (`rbC`). `Bkᵀ` 对证明 $q$ 与 $e$ 递归, 停机靠 $e$ 严格变小.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF5Tr where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Align.Level
open import OCF.Align.UniformNF3Eq using (_≅ˢ_)
open import OCF.Align.Uniform3Base using (Flr; fk; _⊔_; Ev)
open import OCF.Align.Uniform4Base using (Fl)
open import OCF.Align.Uniform4Two
open RestrO
open import OCF.Align.UniformNF5Base
open import OCF.Align.UniformNF5Rules
open import OCF.Align.UniformNF5Strict
open import OCF.Align.UniformNF5Class
open import OCF.Align.UniformNF5ClassF using (inp-map)
open import OCF.Align.UniformNF5Good
```

## §1 上下文的拉回

```agda
bkC : ∀ {j a b ξ} (q : j <ᴵ a) (e : a ≅ᴵ b) → Cx j ξ → Cx (repO (resO q e)) ξ
bkC zero      (s≅ e) D = ptr⁻ e D
bkC (suc q)   (s≅ e) D = bkC q e D
bkC (lim n q) (l≅ f) D = bkC q (f n) D

bkC⁻ : ∀ {j a b ξ} (q : j <ᴵ a) (e : b ≅ᴵ a) → Cx j ξ → Cx (repO (res⁻O q e)) ξ
bkC⁻ zero      (s≅ e) D = ptr e D
bkC⁻ (suc q)   (s≅ e) D = bkC⁻ q e D
bkC⁻ (lim n q) (l≅ f) D = bkC⁻ q (f n) D

rbC : ∀ {j a b ξ} (q : j <ᴵ a) (e : a ≅ᴵ b) (D : Cx j ξ) (u : O (repO (resO q e)) ξ) → runᶜ (bkC q e D) u ≡ runᶜ D (backO (resO q e) u)
rbC zero      (s≅ e) D u = refl
rbC (suc q)   (s≅ e) D u = rbC q e D u
rbC (lim n q) (l≅ f) D u = rbC q (f n) D u

rbC⁻ : ∀ {j a b ξ} (q : j <ᴵ a) (e : b ≅ᴵ a) (D : Cx j ξ) (u : O (repO (res⁻O q e)) ξ) → runᶜ (bkC⁻ q e D) u ≡ runᶜ D (backO (res⁻O q e) u)
rbC⁻ zero      (s≅ e) D u = refl
rbC⁻ (suc q)   (s≅ e) D u = rbC⁻ q e D u
rbC⁻ (lim n q) (l≅ f) D u = rbC⁻ q (f n) D u

cbC : ∀ {j a b ξ} (q : j <ᴵ a) (e : a ≅ᴵ b) (D : Cx j ξ) → Ctxᶜ D → Ctxᶜ (bkC q e D)
cbC zero      (s≅ e) D c = c
cbC (suc q)   (s≅ e) D c = cbC q e D c
cbC (lim n q) (l≅ f) D c = cbC q (f n) D c

cbC⁻ : ∀ {j a b ξ} (q : j <ᴵ a) (e : b ≅ᴵ a) (D : Cx j ξ) → Ctxᶜ D → Ctxᶜ (bkC⁻ q e D)
cbC⁻ zero      (s≅ e) D c = c
cbC⁻ (suc q)   (s≅ e) D c = cbC⁻ q e D c
cbC⁻ (lim n q) (l≅ f) D c = cbC⁻ q (f n) D c

obC : ∀ {j a b ξ ξ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {D : Cx j ξ} {D′ : Cx j ξ′} → D ≈ᶜ D′ → bkC q e D ≈ᶜ bkC q e D′
obC zero      (s≅ e) o = ptr⁻ o
obC (suc q)   (s≅ e) o = obC q e o
obC (lim n q) (l≅ f) o = obC q (f n) o

obC⁻ : ∀ {j a b ξ ξ′} (q : j <ᴵ a) (e : b ≅ᴵ a) {D : Cx j ξ} {D′ : Cx j ξ′} → D ≈ᶜ D′ → bkC⁻ q e D ≈ᶜ bkC⁻ q e D′
obC⁻ zero      (s≅ e) o = ptr o
obC⁻ (suc q)   (s≅ e) o = obC⁻ q e o
obC⁻ (lim n q) (l≅ f) o = obC⁻ q (f n) o

bmᵗ : ∀ {j a b ξ ξ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : O (repO (resO q e)) ξ} {u′ : O (repO (resO q e)) ξ′} → u ⊑ᵗ u′ → backO (resO q e) u ⊑ᵗ backO (resO q e) u′
bmᵗ zero      (s≅ e) h = tr⁻ᵗ-cong h
bmᵗ (suc q)   (s≅ e) h = bmᵗ q e h
bmᵗ (lim n q) (l≅ f) h = bmᵗ q (f n) h

bmᵗ⁻ : ∀ {j a b ξ ξ′} (q : j <ᴵ a) (e : b ≅ᴵ a) {u : O (repO (res⁻O q e)) ξ} {u′ : O (repO (res⁻O q e)) ξ′} → u ⊑ᵗ u′ → backO (res⁻O q e) u ⊑ᵗ backO (res⁻O q e) u′
bmᵗ⁻ zero      (s≅ e) h = trᵗ-cong h
bmᵗ⁻ (suc q)   (s≅ e) h = bmᵗ⁻ q e h
bmᵗ⁻ (lim n q) (l≅ f) h = bmᵗ⁻ q (f n) h
```

## §2 搬运

```agda
Trᵀ  : ∀ {a b φ} (ε : a ≅ᴵ b) {𝓖 : ClT b φ} {𝓧 : ClT a φ} {x : O a φ} → (∀ {C} → 𝓖 C → 𝓧 (ptr ε C)) → (∀ {C} → 𝓖 C → 𝓥 C) → Gᵀ a 𝓧 x → Gᵀ b 𝓖 (trO ε x)
Tr⁻ᵀ : ∀ {a b φ} (ε : a ≅ᴵ b) {𝓖 : ClT a φ} {𝓧 : ClT b φ} {x : O b φ} → (∀ {C} → 𝓖 C → 𝓧 (ptr⁻ ε C)) → (∀ {C} → 𝓖 C → 𝓥 C) → Gᵀ b 𝓧 x → Gᵀ a 𝓖 (tr⁻O ε x)
Bkᵀ  : ∀ {j a b ξ} (q : j <ᴵ a) (e : a ≅ᴵ b) {𝓕 : ClT j ξ} {𝓕′ : ClT (repO (resO q e)) ξ} {u} → (∀ {D} → 𝓕 D → 𝓕′ (bkC q e D)) → (∀ {D} → 𝓕 D → 𝓥 D) → Gᵀ _ 𝓕′ u → Gᵀ j 𝓕 (backO (resO q e) u)
Bk⁻ᵀ : ∀ {j a b ξ} (q : j <ᴵ a) (e : b ≅ᴵ a) {𝓕 : ClT j ξ} {𝓕′ : ClT (repO (res⁻O q e)) ξ} {u} → (∀ {D} → 𝓕 D → 𝓕′ (bkC⁻ q e D)) → (∀ {D} → 𝓕 D → 𝓥 D) → Gᵀ _ 𝓕′ u → Gᵀ j 𝓕 (backO (res⁻O q e) u)

Bkᵀ zero      (s≅ e) M V g = Tr⁻ᵀ e M V g
Bkᵀ (suc q)   (s≅ e) M V g = Bkᵀ q e M V g
Bkᵀ (lim n q) (l≅ f) M V g = Bkᵀ q (f n) M V g

Bk⁻ᵀ zero      (s≅ e) M V g = Trᵀ e M V g
Bk⁻ᵀ (suc q)   (s≅ e) M V g = Bk⁻ᵀ q e M V g
Bk⁻ᵀ (lim n q) (l≅ f) M V g = Bk⁻ᵀ q (f n) M V g

Trᵀ ε H H₂ g0 = g0
Trᵀ ε H H₂ (gs 𝓚 v g clk cgk ho) =
  gs (λ D → 𝓥 D × 𝓚 (ptr ε D)) (λ c → H₂ c , v (H c)) (Trᵀ ε proj₂ proj₁ g)
     (λ {O₁} {C″} (x , c₁) f → cxoᵀ f , clk c₁ (flo-overᵀ (cxoᵀ f) (λ t rt G → flwᵀ f (trO ε t) (R-tr₂ ε ε rt) G)))
     (λ x o (_ , c₁) → x , cgk x (ptr o) c₁)
     (λ (_ , c₁) G k → ho c₁ G k)
Trᵀ ε H H₂ (gl f st) = gl (λ n → Trᵀ ε H H₂ (f n)) (λ n → trᵗ-cong {e = ε} {e′ = ε} (st n))
Trᵀ ε {𝓖 = 𝓖} H H₂ (gi {j = j} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gi (λ D → 𝓥 D × 𝓖₀ (ptr ε D)) (λ c → H₂ c , inc₀ (H c)) (λ D → W (ptr ε D)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez g → Trᵀ ε {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ ptr ε D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
        (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ ptr ε D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
            (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) g)))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) → cx′ , St c₀ (aboveV cx′ (λ t rt → wrap (trO ε t) (R-tr₂ ε ε rt))))
     (λ x o (_ , c₀) → x , cg x (ptr o) c₀)
     (λ h → trᵗ-cong {e = ε} {e′ = ε} (hm h)) (λ d → R-tr₂ ε ε (rf d))
Trᵀ ε {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) =
  gŝ (λ η D → 𝓑 η (ptr ε D)) Bc (Trᵀ ε H H₂ g₀)
     (λ η e → Trᵀ ε {𝓖 = λ D → 𝓖 D × 𝓑 η (ptr ε D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H c , b) (λ (c , b) → H₂ c) (gg η e))
     (R-tr₂ ε ε et) (λ η e η′ e′ d → R-tr₂ ε ε (eg η e η′ e′ d)) (λ η e → trᵗ-cong {e = ε} {e′ = ε} (m η e)) (λ η e η′ e′ u → trᵗ-cong {e = ε} {e′ = ε} (mm η e η′ e′ u))
     (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
Trᵀ ε H H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
  gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-tr₂ ε ε r₁) (λ η e η′ e′ d → R-tr₂ ε ε (r₂ η e η′ e′ d)) (Trᵀ ε H H₂ go) (λ k → Trᵀ ε H H₂ (gO k)) (trᵗ-cong {e = ε} {e′ = ε} mo) (λ k → trᵗ-cong {e = ε} {e′ = ε} (mO k))
Trᵀ ε H H₂ (gw {le = le} 𝓖₁ inc₁ g) =
  gw (λ E → 𝓥 E × 𝓖₁ (ptr ε E)) (λ {C} c → Ctx-wkC C (H₂ c) , inc₁ (H c)) (Trᵀ ε proj₂ proj₁ g)
Trᵀ {φ = φ₀ ⊔ fk zero} ε {𝓖 = 𝓖} H H₂ (gclo {φ = φ₀} 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m mm dt dg ch₀ chS) =
  gclo (λ D → 𝓥 D × 𝓖ᵗ (ptr ε D)) (λ c → H₂ c , inc₁ (H c)) (λ η D → 𝓥 D × 𝓖ᵍ η (ptr ε D))
     (λ e x o (_ , c₁) → x , Bc e x (ptr o) c₁)
     (Trᵀ ε proj₂ proj₁ gt) (λ η → Trᵀ ε proj₂ proj₁ (gg η))
     (R-tr₂ ε ε rt) (λ η η′ e → R-tr₂ ε ε (rg η η′ e))
     (λ η h → trᵗ-cong {e = ε} {e′ = ε} (m η h)) (λ η η′ h u → trᵗ-cong {e = ε} {e′ = ε} (mm η η′ h u))
     (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
     (λ (_ , c₁) G x o → x , ch₀ c₁ G x (ptr o)) (λ η (_ , c₁) G x o → x , chS η c₁ G x (ptr o))
Trᵀ {a} {b} {φ} ε {𝓖} {𝓧} H H₂ (gΩ {m = m} {r = r} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gΩ (λ ξ D → 𝓥 D × 𝓖₀ ξ (ptr ε D))
     (λ ξ c x o → x , inc₀ ξ (H c) x (ptr o))
     (λ ξ D → bkC r ε (W ξ (ptr ε D)))
     (λ ξ {D} (x , c₀) u ru → subst (λ v → runᶜ (bkC r ε (W ξ (ptr ε D))) u ≅ˢ runᶜ D (trO ε (h ξ (intoU (<→◃ r) (backO (resO r ε) v))))) (sym (out-intoU (<→◃ r′) u))
          (subst (λ v → v ≅ˢ runᶜ D (trO ε (h ξ (intoU (<→◃ r) (backO (resO r ε) u))))) (sym (rbC r ε (W ξ (ptr ε D)) u)) (Wf ξ c₀ (backO (resO r ε) u) (R-back r ε ru))))
     (λ 𝓔′ inc″ ξ z rz g → subst (λ v → Gᵀ b (𝓔′ ξ) (trO ε (h ξ (intoU (<→◃ r) (backO (resO r ε) v))))) (sym (out-intoU (<→◃ r′) z))
        (Trᵀ ε {𝓖 = 𝓔′ ξ} {𝓧 = 𝓧₃ 𝓔′ ξ} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ ξ c))
           (hb (𝓧₃ 𝓔′) (λ ξ₁ {E} → λ { (D , c , refl) → proj₂ (inc″ ξ₁ c) }) ξ (backO (resO r ε) z) (R-back r ε rz)
               (intoG (<→◃ r) (Bkᵀ r ε {𝓕′ = (λ D → bkC r ε (W ξ (ptr ε D))) ⟪ 𝓔′ ξ ⟫ᵀ}
                   (λ { (x , E , (D , c , refl) , o) → cbC r ε _ x , D , c , obC r ε o }) proj₁ (outG (<→◃ r′) g))))))
     (λ ξ {D} (x , c₀) → cbC r ε _ (Wv ξ c₀))
     (λ ξ {D} {C′} (x , c₀) (aboveΩ cx′ wrap) → cx′ , St ξ c₀ (aboveΩ cx′ (λ t rt →
        let Wp = wrap (trO ε t) (R-tr₂ ε ε rt)
            u = proj₁ Wp
            ru = proj₁ (proj₂ Wp)
            fu = proj₁ (proj₂ (proj₂ Wp))
            d = proj₂ (proj₂ (proj₂ Wp))
        in backO (resO r ε) u , R-back r ε ru , Fl-back r ε fu , subst (λ v → runᶜ C′ (trO ε t) ≅ˢ v) (rbC r ε (W ξ (ptr ε D)) u) d)))
     (λ ξ ξ′ x o (_ , c₀) → x , cg ξ ξ′ x (ptr o) c₀)
     (λ {ξ} {ξ′} {z} {z′} u → subst₂ (λ v v′ → trO ε (h ξ (intoU (<→◃ r) (backO (resO r ε) v))) ⊑ᵗ trO ε (h ξ′ (intoU (<→◃ r) (backO (resO r ε) v′)))) (sym (out-intoU (<→◃ r′) z)) (sym (out-intoU (<→◃ r′) z′))
          (trᵗ-cong {e = ε} {e′ = ε} (hm (bmᵗ r ε u))))
     (λ ξ ξ′ d z z′ l → subst₂ (λ v v′ → Rᵒ b b (trO ε (h ξ (intoU (<→◃ r) (backO (resO r ε) v)))) (trO ε (h ξ′ (intoU (<→◃ r) (backO (resO r ε) v′))))) (sym (out-intoU (<→◃ r′) z)) (sym (out-intoU (<→◃ r′) z′))
          (R-tr₂ ε ε (rf ξ ξ′ d _ _ (R-back r ε l))))
  where
  r′ = ltO (resO r ε)
  𝓧₃ : (∀ ξ → ClT b (ξ ⊔ φ)) → ∀ ξ → ClT a (ξ ⊔ φ)
  𝓧₃ 𝓔′ ξ E = Σ _ λ D → 𝓔′ ξ D × (E ≡ ptr ε D)

Tr⁻ᵀ ε H H₂ g0 = g0
Tr⁻ᵀ ε H H₂ (gs 𝓚 v g clk cgk ho) =
  gs (λ D → 𝓥 D × 𝓚 (ptr⁻ ε D)) (λ c → H₂ c , v (H c)) (Tr⁻ᵀ ε proj₂ proj₁ g)
     (λ {O₁} {C″} (x , c₁) f → cxoᵀ f , clk c₁ (flo-overᵀ (cxoᵀ f) (λ t rt G → flwᵀ f (tr⁻O ε t) (R-tr⁻₂ ε ε rt) G)))
     (λ x o (_ , c₁) → x , cgk x (ptr⁻ o) c₁)
     (λ (_ , c₁) G k → ho c₁ G k)
Tr⁻ᵀ ε H H₂ (gl f st) = gl (λ n → Tr⁻ᵀ ε H H₂ (f n)) (λ n → tr⁻ᵗ-cong {e = ε} {e′ = ε} (st n))
Tr⁻ᵀ ε {𝓖 = 𝓖} H H₂ (gi {j = j} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gi (λ D → 𝓥 D × 𝓖₀ (ptr⁻ ε D)) (λ c → H₂ c , inc₀ (H c)) (λ D → W (ptr⁻ ε D)) (λ (x , c₀) u eu → Wf c₀ u eu)
     (λ 𝓔′ inc″ z ez g → Tr⁻ᵀ ε {𝓖 = 𝓔′} {𝓧 = λ E → Σ _ λ D → 𝓔′ D × (E ≡ ptr⁻ ε D)} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ c))
        (hb (λ E → Σ _ λ D → 𝓔′ D × (E ≡ ptr⁻ ε D)) (λ { (D , c , refl) → proj₂ (inc″ c) }) z ez
            (Good-mono (inp-map j (λ { (x , E , (D , c , refl) , o) → x , D , c , o })) g)))
     (λ (x , c₀) → Wv c₀)
     (λ (x , c₀) (aboveV cx′ wrap) → cx′ , St c₀ (aboveV cx′ (λ t rt → wrap (tr⁻O ε t) (R-tr⁻₂ ε ε rt))))
     (λ x o (_ , c₀) → x , cg x (ptr⁻ o) c₀)
     (λ h → tr⁻ᵗ-cong {e = ε} {e′ = ε} (hm h)) (λ d → R-tr⁻₂ ε ε (rf d))
Tr⁻ᵀ ε {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gŝ 𝓑 Bc g₀ gg et eg m mm d₀ dE ch₀ chS) =
  gŝ (λ η D → 𝓑 η (ptr⁻ ε D)) Bc (Tr⁻ᵀ ε H H₂ g₀)
     (λ η e → Tr⁻ᵀ ε {𝓖 = λ D → 𝓖 D × 𝓑 η (ptr⁻ ε D)} {𝓧 = λ E → 𝓧 E × 𝓑 η E} (λ (c , b) → H c , b) (λ (c , b) → H₂ c) (gg η e))
     (R-tr⁻₂ ε ε et) (λ η e η′ e′ d → R-tr⁻₂ ε ε (eg η e η′ e′ d)) (λ η e → tr⁻ᵗ-cong {e = ε} {e′ = ε} (m η e)) (λ η e η′ e′ u → tr⁻ᵗ-cong {e = ε} {e′ = ε} (mm η e η′ e′ u))
     (λ c G → d₀ (H c) G) (λ η e c b G → dE η e (H c) b G) (λ c G → ch₀ (H c) G) (λ η e c b G → chS η e (H c) b G)
Tr⁻ᵀ ε H H₂ (gĉ ys hy dy G₀ l₀ Gg lE ez ezg r₁ r₂ go gO mo mO) =
  gĉ ys hy dy G₀ l₀ Gg lE ez ezg (R-tr⁻₂ ε ε r₁) (λ η e η′ e′ d → R-tr⁻₂ ε ε (r₂ η e η′ e′ d)) (Tr⁻ᵀ ε H H₂ go) (λ k → Tr⁻ᵀ ε H H₂ (gO k)) (tr⁻ᵗ-cong {e = ε} {e′ = ε} mo) (λ k → tr⁻ᵗ-cong {e = ε} {e′ = ε} (mO k))
Tr⁻ᵀ ε H H₂ (gw {le = le} 𝓖₁ inc₁ g) =
  gw (λ E → 𝓥 E × 𝓖₁ (ptr⁻ ε E)) (λ {C} c → Ctx-wkC C (H₂ c) , inc₁ (H c)) (Tr⁻ᵀ ε proj₂ proj₁ g)
Tr⁻ᵀ {φ = φ₀ ⊔ fk zero} ε {𝓖 = 𝓖} H H₂ (gclo {φ = φ₀} 𝓖ᵗ inc₁ 𝓖ᵍ Bc gt gg rt rg m mm dt dg ch₀ chS) =
  gclo (λ D → 𝓥 D × 𝓖ᵗ (ptr⁻ ε D)) (λ c → H₂ c , inc₁ (H c)) (λ η D → 𝓥 D × 𝓖ᵍ η (ptr⁻ ε D))
     (λ e x o (_ , c₁) → x , Bc e x (ptr⁻ o) c₁)
     (Tr⁻ᵀ ε proj₂ proj₁ gt) (λ η → Tr⁻ᵀ ε proj₂ proj₁ (gg η))
     (R-tr⁻₂ ε ε rt) (λ η η′ e → R-tr⁻₂ ε ε (rg η η′ e))
     (λ η h → tr⁻ᵗ-cong {e = ε} {e′ = ε} (m η h)) (λ η η′ h u → tr⁻ᵗ-cong {e = ε} {e′ = ε} (mm η η′ h u))
     (λ (_ , c₁) G k → dt c₁ G k) (λ η (_ , c₁) G k → dg η c₁ G k)
     (λ (_ , c₁) G x o → x , ch₀ c₁ G x (ptr⁻ o)) (λ η (_ , c₁) G x o → x , chS η c₁ G x (ptr⁻ o))
Tr⁻ᵀ {a = b} {b = a} {φ} ε {𝓖} {𝓧} H H₂ (gΩ {m = m} {r = r} {h = h} 𝓖₀ inc₀ W Wf hb Wv St cg hm rf) =
  gΩ (λ ξ D → 𝓥 D × 𝓖₀ ξ (ptr⁻ ε D))
     (λ ξ c x o → x , inc₀ ξ (H c) x (ptr⁻ o))
     (λ ξ D → bkC⁻ r ε (W ξ (ptr⁻ ε D)))
     (λ ξ {D} (x , c₀) u ru → subst (λ v → runᶜ (bkC⁻ r ε (W ξ (ptr⁻ ε D))) u ≅ˢ runᶜ D (tr⁻O ε (h ξ (intoU (<→◃ r) (backO (res⁻O r ε) v))))) (sym (out-intoU (<→◃ r′) u))
          (subst (λ v → v ≅ˢ runᶜ D (tr⁻O ε (h ξ (intoU (<→◃ r) (backO (res⁻O r ε) u))))) (sym (rbC⁻ r ε (W ξ (ptr⁻ ε D)) u)) (Wf ξ c₀ (backO (res⁻O r ε) u) (R-back⁻ r ε ru))))
     (λ 𝓔′ inc″ ξ z rz g → subst (λ v → Gᵀ b (𝓔′ ξ) (tr⁻O ε (h ξ (intoU (<→◃ r) (backO (res⁻O r ε) v))))) (sym (out-intoU (<→◃ r′) z))
        (Tr⁻ᵀ ε {𝓖 = 𝓔′ ξ} {𝓧 = 𝓧₃ 𝓔′ ξ} (λ {D} c → D , c , refl) (λ c → proj₁ (inc″ ξ c))
           (hb (𝓧₃ 𝓔′) (λ ξ₁ {E} → λ { (D , c , refl) → proj₂ (inc″ ξ₁ c) }) ξ (backO (res⁻O r ε) z) (R-back⁻ r ε rz)
               (intoG (<→◃ r) (Bk⁻ᵀ r ε {𝓕′ = (λ D → bkC⁻ r ε (W ξ (ptr⁻ ε D))) ⟪ 𝓔′ ξ ⟫ᵀ}
                   (λ { (x , E , (D , c , refl) , o) → cbC⁻ r ε _ x , D , c , obC⁻ r ε o }) proj₁ (outG (<→◃ r′) g))))))
     (λ ξ {D} (x , c₀) → cbC⁻ r ε _ (Wv ξ c₀))
     (λ ξ {D} {C′} (x , c₀) (aboveΩ cx′ wrap) → cx′ , St ξ c₀ (aboveΩ cx′ (λ t rt →
        let Wp = wrap (tr⁻O ε t) (R-tr⁻₂ ε ε rt)
            u = proj₁ Wp
            ru = proj₁ (proj₂ Wp)
            fu = proj₁ (proj₂ (proj₂ Wp))
            d = proj₂ (proj₂ (proj₂ Wp))
        in backO (res⁻O r ε) u , R-back⁻ r ε ru , Fl-back⁻ r ε fu , subst (λ v → runᶜ C′ (tr⁻O ε t) ≅ˢ v) (rbC⁻ r ε (W ξ (ptr⁻ ε D)) u) d)))
     (λ ξ ξ′ x o (_ , c₀) → x , cg ξ ξ′ x (ptr⁻ o) c₀)
     (λ {ξ} {ξ′} {z} {z′} u → subst₂ (λ v v′ → tr⁻O ε (h ξ (intoU (<→◃ r) (backO (res⁻O r ε) v))) ⊑ᵗ tr⁻O ε (h ξ′ (intoU (<→◃ r) (backO (res⁻O r ε) v′)))) (sym (out-intoU (<→◃ r′) z)) (sym (out-intoU (<→◃ r′) z′))
          (tr⁻ᵗ-cong {e = ε} {e′ = ε} (hm (bmᵗ⁻ r ε u))))
     (λ ξ ξ′ d z z′ l → subst₂ (λ v v′ → Rᵒ b b (tr⁻O ε (h ξ (intoU (<→◃ r) (backO (res⁻O r ε) v)))) (tr⁻O ε (h ξ′ (intoU (<→◃ r) (backO (res⁻O r ε) v′))))) (sym (out-intoU (<→◃ r′) z)) (sym (out-intoU (<→◃ r′) z′))
          (R-tr⁻₂ ε ε (rf ξ ξ′ d _ _ (R-back⁻ r ε l))))
  where
  r′ = ltO (res⁻O r ε)
  𝓧₃ : (∀ ξ → ClT b (ξ ⊔ φ)) → ∀ ξ → ClT a (ξ ⊔ φ)
  𝓧₃ 𝓔′ ξ E = Σ _ λ D → 𝓔′ ξ D × (E ≡ ptr⁻ ε D)
```
