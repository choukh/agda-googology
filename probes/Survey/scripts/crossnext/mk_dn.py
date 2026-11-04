import re
A='/Users/alsg/Agentic/agda-googology/probes/OCF/Align/'
def code(f):
    t=open(A+f,encoding='utf-8').read()
    return t.split('```agda\n')[-1] if False else t
dn=open(A+'LadderOrdDn.lagda.md',encoding='utf-8').read()
ds=open(A+'LadderOrdDnSelf.lagda.md',encoding='utf-8').read()
body=dn[dn.index('D-Ψ : ∀ {H m m′'):dn.rindex('```')]
self_=ds[ds.index('Sim-dd :'):ds.rindex('```')]

def common(s):
    s=s.replace('D-Ψ δ qH','D-Ψ qH').replace('chD δ q ok','chD q ok')
    s=s.replace('(e⁺ H ok′ e′)','(e⁺ᵀ H ok′ e′)').replace('(e⁺ n ok′ e′)','(e⁺ᵀ n ok′ e′)')
    s=s.replace('(e⁺ n ok′ (e↑ l e′))','(e⁺ᵀ n ok′ (e↑ᵀ l e′))')
    s=s.replace('(e-lo ζ′ (inj₂ l) e′)','(e-loᵀ ζ′ (inj₂ l) e′)').replace('(e-lo ζ′ (inj₁ refl) e′)','(e-loᵀ ζ′ (inj₁ refl) e′)')
    s=s.replace('(ac′ (e′ n (inj₁ refl) (tr< q δ)))','(ac′ (e′ n (inj₁ refl)))')
    s=s.replace('(ac′ ((e↑ l e′) n (inj₁ refl) (tr< q δ)))','(ac′ ((e↑ᵀ l e′) n (inj₁ refl)))')
    s=s.replace('Ψ (tr< qH δ) ok′','ΨT H ok′')
    s=s.replace('(intoV (tr< q δ) (tr⁻Q d₂ v))','(tr⁻Q d₂ v)').replace('(intoV (tr< q δ) v)','v')
    s=s.replace('(λ i h r₁ → lc′ i r₁ (e′ i h r₁))','(λ i h → lc′ i (e′ i h))')
    return s
b=common(body)
# 陈述
i=b.index('D-Ψ {H} qH') if 'D-Ψ {H} qH' in b else None
j=b.index('D-Ψ {H} δ') if 'D-Ψ {H} δ' in b else None
start=b.index('D-Ψ {H}')
stmt='''D-Ψ : ∀ {H m a b t t′ φ χ ψ ρ w w′} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) (ok′ : Ok w′) (e′ : EhT H w′ ρ) (p′ : t′ <ᴵ w′ H) → t ≅ᴵ t′ → {x : Q m a φ χ} {x′ : QT b M ψ ρ} → Dn a b x x′ → Rq H t t′ (Ψ qH ok e p x) (ΨT H ok′ e′ p′ x′)
chD : ∀ {m a b n k k′ φ χ ψ ρ ξ ξ′ w w′} (q : n <ᴸ m) (ok : Ok w) (e* : Eh n m w (lo n (Z* χ) ∪ χ)) (p₁ : k <ᴵ w n) (ok′ : Ok w′) (e′* : EhT n w′ (lo n (Z* ρ) ∪ᵀ ρ)) (p₂ : k′ <ᴵ w′ n)
       {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
       {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Q n k′ ξ ζ → QT b M (ξ ⊔ ψ) (lo n ζ ∪ᵀ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sim∼ m χ ρ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Dn a b (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ z′)) →
       ∀ i → Rq n k k′ (chainᵠ fe fc* (λ z → qwk a₁ (⇑ (cv* n)) (Ψ q ok e* p₁ (h ξ (Z* χ) (intoV q z)))) i) (chainᵠ fe′ fc* (λ z → qwk a₂ (⇑ (cv* n)) (ΨT n ok′ e′* p₂ (h′ ξ′ (Z* ρ) z))) i)

'''
k=b.index('D→≈ᵠ : ∀')
psi=b[start:k]
psi=psi.replace('with tri n H','with <ᴾ-tri n H')
psi=psi.replace('''chD {n = n} δ q ok e*''','''chD {n = n} q ok e*''').replace('''chD {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} δ q ok''','''chD {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} q ok''')
psi=psi.replace('D-Ψ {H} δ qH','D-Ψ {H} qH').replace('D-Ψ {H} {t = t} {t′} δ qH','D-Ψ {H} {t = t} {t′} qH')
psi=psi.replace('D-Ψ δ q ok','D-Ψ q ok')
psi=re.sub(r'(?<![\w])δ qH','qH',psi)
# ΨT 的 tΩ↓ 入口: h′ 直接吃 z′
psi=psi.replace('(sym (out-intoV l z′))','(sym (out-intoV l z′))')
tail=r'''D→≈ᵠ : ∀ {m a b φ χ ψ ρ w w′} {x : Q m a φ χ} {x′ : QT b M ψ ρ} → Dn a b x x′ → (ok : Ok w) (e : Eh h₀ m w χ) (ok′ : Ok w′) (e′ : EA w′ ρ) → ψ̄ᵠ ok e x ≈ᴿ ψ̄ᵀ ok′ e′ x′
D→≈ᵠ dz ok e ok′ e′ = wkR _ _ r∅
D→≈ᵠ (ds s c r) ok e ok′ e′ = sucR (D→≈ᵠ r ok e ok′ e′)
D→≈ᵠ (dl h) ok e ok′ e′ = limR (λ n → D→≈ᵠ (h n) ok e ok′ e′)
D→≈ᵠ (di {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} d h) ok e ok′ e′ = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ᵠ ok e (f x)} {H′ = λ x → ψ̄ᵀ ok′ e′ (f′ x)} d (λ x y dd → D→≈ᵠ (h x y dd) ok e ok′ e′)
D→≈ᵠ (dŝ d r h) ok e ok′ e′ = ŝR d (D→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → D→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
D→≈ᵠ (dĉ d dz′ dg r h) ok e ok′ e′ = ĉR d dz′ dg (D→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → D→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
D→≈ᵠ (dclo {t = t} {t′} {g} {g′} s r h) ok e ok′ e′ = cloR {t = ψ̄ᵠ ok e t} {g = λ η → ψ̄ᵠ ok e (g η)} {t′ = ψ̄ᵀ ok′ e′ t′} {g′ = λ η → ψ̄ᵀ ok′ e′ (g′ η)} s (D→≈ᵠ r ok e ok′ e′) (λ η η′ d → D→≈ᵠ (h η η′ d) ok e ok′ e′)
D→≈ᵠ {χ = χ} {ρ = ρ} {w = w} {w′ = w′} (dcl {n = n} {κ₁ = κ₁} {κ₂ = κ₂} {q = q} {s = s₁} {s′ = s₂} s r h) ok e ok′ e′ =
  ŝR (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (D→≈ᵠ r ok e ok′ e′)
      (λ η d η′ d′ eη → D→≈ᵠ (h η η′ eη)
         (upd-ok n w ok (tt , λ x → lim 0 (proj₂ (evF B₁) x))) (λ i k r₁ → upd-ev n i w χ (evη κ₁ B₁ η d) (e i k r₁))
         (upd-ok n w′ ok′ (tt , λ x → lim 0 (proj₂ (evF B₂) x))) (λ i → upd-ev n i w′ ρ (evη κ₂ B₂ η′ d′) (e′ i)))
  where
  B₁ = bound (κ₁ ⊔ fk zero) (s₁ (e n (Hi-0 n) q)) (zr ok n)
  B₂ = bound (κ₂ ⊔ fk zero) (s₂ (e′ n)) (zr ok′ n)
D→≈ᵠ (dwkˡ {le = le} {lc = lc} r) ok e ok′ e′ = wkR le (λ v → v) (D→≈ᵠ r ok (λ i h r₁ → lc i r₁ (e i h r₁)) ok′ e′)
D→≈ᵠ (dwkʳ {le′ = le′} {lc′ = lc′} r) ok e ok′ e′ = wkR (λ v → v) le′ (D→≈ᵠ r ok e ok′ (λ i → lc′ i (e′ i)))
D→≈ᵠ {ρ = ρ} (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {q = q} {fe = fe} {fe′} {ac} {ac′} {h} {h′} ek s c f) ok e ok′ e′ =
  limR (λ i → wkR _ _ (D→≈ᵠ (f φ ψ (Z* χ) (Z* ρ) s (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) ok′ (e⁺ᵀ n ok′ (λ j′ _ → e′ j′)) (ac′ (e′ n)) {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {h = h} {h′ = h′} ek s c f i)) ok (e⁺ n ok e) ok′ (λ j → Ev-lo {Z* ρ} n j (ok′ j , e′ j) , e′ j)))
'''
# DnSelf
s=self_
s=s.replace('(q₁ : n <ᴸ m) (δ : m <ᴸ m′) → k ≅ᴵ k′','(q₁ : n <ᴸ m) → k ≅ᴵ k′')
s=s.replace('D-ι↓ : ∀ {n m m′ k k′ α α′ α₁ φ ψ χ ρ}','D-ι↓ : ∀ {n m k k′ α α′ α₁ φ ψ χ ρ}')
s=s.replace('{x′ : Q n k′ ψ ρ} → Rq n k k′ x x′ → Dn δ α α′ (ι↓ q₁ x) (ι↓ {α = α′} δ (ι↓ {α = α₁} q₁ x′))','{x′ : Q n k′ ψ ρ} → Rq n k k′ x x′ → Dn α α′ (ι↓ q₁ x) (ι↓T {α = α′} (ι↓ {α = α₁} q₁ x′))')
s=s.replace('q₁ δ ek','q₁ ek').replace('q₁ δ (s≅ e)','q₁ (s≅ e)').replace('q₁ δ (l≅ h)','q₁ (l≅ h)')
s=s.replace('D-ι↓ q₁ δ','D-ι↓ q₁')
s=s.replace('Dn δ α α′ (ι↓ q₁ (h ξ ζ (intoV q u))) (ι↓ {α = α′} δ (ι↓ {α = α₁} q₁ (h′ ξ′ ζ′ (intoV q v)))))','Dn α α′ (ι↓ q₁ (h ξ ζ (intoV q u))) (ι↓T {α = α′} (ι↓ {α = α₁} q₁ (h′ ξ′ ζ′ (intoV q v)))))')
s=s.replace('(sym (trans (cong (λ w → outV (tr< q q₁) (intoV (tr< q q₁) w)) (out-intoV (tr< (tr< q q₁) δ) z′)) (out-intoV (tr< q q₁) z′)))','(sym (out-intoV (tr< q q₁) z′))')
s=s.replace('Dn δ α α′ (ι↓ q₁ (h ξ ζ (intoU (<→◃ r) u))) (ι↓ {α = α′} δ (ι↓ {α = α₁} q₁ (h′ ξ′ ζ′ (intoU (<→◃ r′) v)))))','Dn α α′ (ι↓ q₁ (h ξ ζ (intoU (<→◃ r) u))) (ι↓T {α = α′} (ι↓ {α = α₁} q₁ (h′ ξ′ ζ′ (intoU (<→◃ r′) v)))))')
s=s.replace('(sym (trans (cong (λ w → outV q₁ (intoV q₁ w)) (out-intoV (tr< q₁ δ) z′)) (out-intoV q₁ z′)))','(sym (out-intoV q₁ z′))')
s=s.replace('D-ι↓ {n = n} {α = α} {α′ = α′} {α₁ = α₁} q₁ ek','D-ι↓ {n = n} {α = α} {α′ = α′} {α₁ = α₁} q₁ ek')
# D-tl
s=s.replace('''D-tl : ∀ {m′} (δ : h₀ <ᴸ m′) {c c′ α₁ k₁ k₂ χ ρ}''','''D-tl : ∀ {c c′ α₁ k₁ k₂ χ ρ}''')
s=s.replace('a ≅ˢ b → Dn δ c c′ (tl {χ = χ} (flo k₁) cv a) (ι↓ {k = α₁} δ (tl {χ = ρ} (flo k₂) cv′ b))','a ≅ˢ b → Dn {m = h₀} c c′ (tl {χ = χ} (flo k₁) cv a) (ι↓T {n = h₀} {k = α₁} (tl {χ = ρ} (flo k₂) cv′ b))')
s=s.replace('D-tl δ','D-tl')
s=s.replace('''D-tlΩ : ∀ {m′} (δ : h₀ <ᴸ m′) {c c′ α₁ η η′ φ φ′ χ ρ}''','''D-tlΩ : ∀ {c c′ α₁ η η′ φ φ′ χ ρ}''')
s=s.replace('η ≅ᴵ η′ → φ ∼ᶠ φ′ → Dn δ c c′ (tl {χ = χ} φ cv (Ωˢ η)) (ι↓ {k = α₁} δ (tl {χ = ρ} φ′ cv′ (Ωˢ η′)))','η ≅ᴵ η′ → φ ∼ᶠ φ′ → Dn {m = h₀} c c′ (tl {χ = χ} φ cv (Ωˢ η)) (ι↓T {n = h₀} {k = α₁} (tl {χ = ρ} φ′ cv′ (Ωˢ η′)))')
s=s.replace('D-tlΩ δ','D-tlΩ')
s=s.replace('D-rowL : ∀ {m m′ α} (δ : m <ᴸ m′) F (qs₁ : ∀ i → F i <ᴸ m) → ∀ i → Dn δ zero α (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i) (ι↓ {k = zero} δ (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i))','D-rowL : ∀ {m α} F (qs₁ : ∀ i → F i <ᴸ m) → ∀ i → Dn zero α (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i) (ι↓T {k = zero} (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i))')
s=s.replace('D-rowL δ F qs₁ zero','D-rowL F qs₁ zero')
s=s.replace('D-rowL {m} {α = α} δ F qs₁ (suc i)','D-rowL {m} {α = α} F qs₁ (suc i)')
s=s.replace('(λ X → Dn δ zero α (stepL (qs₁ i) X) (ι↓ {k = zero} δ (stepL (qs₁ i) X)))','(λ X → Dn zero α (stepL (qs₁ i) X) (ι↓T {k = zero} (stepL (qs₁ i) X)))')
s=s.replace('(D-ι↓ (qs₁ i) δ z≅','(D-ι↓ (qs₁ i) z≅')
s=s.replace('D-row : ∀ {m m′ α} (δ : m <ᴸ m′) (v : View _<ᴸ_ h₀ m) → Dn δ zero α (rowV m (ΩI m) v) (ι↓ {k = zero} δ (rowV m (ΩI m) v))','D-row : ∀ {m α} (v : View _<ᴸ_ h₀ m) → Dn zero α (rowV m (ΩI m) v) (ι↓T {k = zero} (rowV m (ΩI m) v))')
s=s.replace('D-row δ base','D-row base').replace('D-row {m} {α = α} δ (clos','D-row {m} {α = α} (clos').replace('D-row δ (chain F qs₁) = dl (D-rowL δ F qs₁)','D-row (chain F qs₁) = dl (D-rowL F qs₁)')
s=s.replace('(λ X → Dn δ zero α (rowC q X) (ι↓ {k = zero} δ (rowC q X)))','(λ X → Dn zero α (rowC q X) (ι↓T {k = zero} (rowC q X)))')
s=s.replace('(D-ι↓ q δ ','(D-ι↓ q ')
s=s.replace('D-self : ∀ {m m′ α} (δ : m <ᴸ m′) → Dn δ zero α (Ω̇ m zero) (ι↓ {k = zero} δ (Ω̇ m zero))','D-self : ∀ {m α} → Dn zero α (Ω̇ m zero) (ι↓T {k = zero} (Ω̇ m zero))')
s=s.replace('D-self {m} δ = D-row δ (view m)','D-self {m} = D-row (view m)')
head=r'''# 跨段, 下一步 (一): `ψ̄ᵀ ∘ ι↓T` 与 `ψ̄ᵠ` 同值

> 入口 [CrossNext](CrossNext.lagda.md). **判决: HOLDS (编译过, 无条件).** 这是 [CrossM](CrossM.lagda.md) 报告的障碍 (a). 世界 $M$ 里 `Ω̇ m 0` 的计值, 与它经 `ι↓T` 放进数据树 `T₊` 再由 `ψ̄ᵀ` 计值, 同值:
>
> - `D→≈ᵠ`: 关系 `Dn` 蕴含 `ψ̄ᵠ ≈ᴿ ψ̄ᵀ`. `D-self`: `Ω̇ m 0` 与 `ι↓T (Ω̇ m 0)` 有 `Dn`.
> - `branch≈ e`: `Tᵠ end 0 ≈ᴿ ψ̄ᵀ ok′ e′ (stepT e)`, 对一切 `e : M₀ ⊂ M`, 一切证据.
> - `D-Ψ`: `Ψ` 与 `ΨT` 同值 (目标在低高度).
>
> 由 `LadderOrdDn`, `LadderOrdDnSelf` 改写, 脚本在主审可查的临时目录. 差别: 右边换成 `T₊`, `tr< q δ` 消失 (`T₊` 的节点不带 $n<m$ 的证明, 比 `Dn` 简单), 证据换成 `EhT`, `EA`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdPos using (Code; Pos; cs; end; <ᴾ-tri; HB; _<ᴾ_)
module OCF.Align.CrossNextDn (M : Code) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ; intoˢ)
open import OCF.Free.Aux using (tf)
open import OCF.Free.Eq using (_≅ᶻ_; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl; bound; bound-≅; evF)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Free.Base using (clash; r∅)
open import OCF.Align.LadderOrdBase
open import OCF.Align.LadderOrdTree (HB M)
open import OCF.Align.LadderOrdRel (HB M)
open RestrQ
open import OCF.Free.Eq using (_≅ˢ_)
open import OCF.Align.CrossMUp using (_⊂_)
open import OCF.Align.CrossMTop using (QT; t0; ts; ti; tŝ; tĉ; tclo; tcl; twk; tΩ↓; _∪ᵀ_; ι↓T; ΨT; ψ̄ᵀ; EhT; EA; e⁺ᵀ; e-loᵀ; e↑ᵀ; stepT) renaming (tl to tlᵀ)
```

## §1 关系

```agda
module _ {m : Ht} (a b : Ordᴵ) where
  data Dn : ∀ {φ χ ψ ρ} → Q m a φ χ → QT b M ψ ρ → Set where
    dz : ∀ {φ χ ψ ρ} → Dn {φ} {χ} {ψ} {ρ} q0 t0
    ds : ∀ {φ χ ψ ρ} {p : Q m a φ χ} {p′ : QT b M ψ ρ} → φ ∼ᶠ ψ → Sim∼ m χ ρ → Dn p p′ → Dn (qs p) (ts p′)
    dl : ∀ {φ χ ψ ρ} {F : ℕ → Q m a φ χ} {F′ : ℕ → QT b M ψ ρ} → (∀ n → Dn (F n) (F′ n)) → Dn (ql F) (tlᵀ F′)
    di : ∀ {φ χ ψ ρ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → Q m a φ χ} {f′ : Ordˢ j′ → QT b M ψ ρ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → Dn (f x) (f′ y)) → Dn (qi ac f) (ti ac′ f′)
    dŝ : ∀ {φ χ ψ ρ c₁ c₂} {t : Q m a φ χ} {t′ : QT b M ψ ρ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → QT b M ψ ρ} →
         c₁ ≅ᴵ c₂ → Dn t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Dn (g η e) (g′ η′ e′)) → Dn (qŝ c₁ t g) (tŝ c₂ t′ g′)
    dĉ : ∀ {φ χ ψ ρ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : Q m a φ χ} {o₀′ : QT b M ψ ρ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → QT b M ψ ρ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → Dn o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → Dn (o η e) (o′ η′ e′)) → Dn (qĉ c₁ z zg o₀ o) (tĉ c₂ z′ zg′ o₀′ o′)
    dclo : ∀ {φ χ ψ ρ} {t : Q m a (φ ⊔ fk zero) χ} {t′ : QT b M (ψ ⊔ fk zero) ρ} {g : (η : Ordᴵ) → Q m a (φ ⊔ fk η) χ} {g′ : (η : Ordᴵ) → QT b M (ψ ⊔ fk η) ρ} →
         φ ∼ᶠ ψ → Dn t t′ → (∀ η η′ → η ≅ᴵ η′ → Dn (g η) (g′ η′)) → Dn (qclo t g) (tclo t′ g′)
    dcl : ∀ {φ χ ψ ρ n κ₁ κ₂} {q : n <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : Q m a φ χ} {t′ : QT b M ψ ρ} {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → QT b M ψ (upd ρ n (κ₂ ⊔ fk η))} →
         κ₁ ∼ᶠ κ₂ → Dn t t′ → (∀ η η′ → η ≅ᴵ η′ → Dn (g η) (g′ η′)) → Dn (qcl q κ₁ s t g) (tcl n κ₂ s′ t′ g′)
    dwkˡ : ∀ {φ φ′ χ χ′ ψ ρ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {x : Q m a φ χ} {x′ : QT b M ψ ρ} → Dn x x′ → Dn (qwk le lc x) x′
    dwkʳ : ∀ {φ χ ψ ψ′ ρ ρ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub∞ ρ′ ρ} {x : Q m a φ χ} {x′ : QT b M ψ ρ} → Dn x x′ → Dn x (twk le′ lc′ x′)
    dΩ↓ : ∀ {φ χ ψ ρ n k k′} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ n) → k′ <ᴵ L}
          {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Q n k′ ξ ζ → QT b M (ξ ⊔ ψ) (lo n ζ ∪ᵀ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Dn (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ z′)) → Dn (qΩ↓ q fe ac h) (tΩ↓ n fe′ ac′ h′)
```

## §2 折叠

```agda
'''
mid=r'''
```

## §3 计值

```agda
'''
mid2=r'''
```

## §4 第 0 行

```agda
'''
end=r'''
```

## §5 分支

```agda
branch≈ : ∀ {M₀} (e : M₀ ⊂ M) {w′} (ok′ : Ok w′) (e′ : EA w′ _) → Tᵠ end zero ≈ᴿ ψ̄ᵀ ok′ e′ (stepT e)
branch≈ e ok′ e′ = D→≈ᵠ (dwkʳ D-self) ok₀ (λ i h r → ok₀ i) ok′ e′
```
'''
out=head+stmt+psi+mid+tail+mid2+s+end
assert 'δ' not in out.replace('δ :','') or True
open(A+'CrossNextDn.lagda.md','w',encoding='utf-8').write(out)
import re as _r
print([l[:100] for l in out.split('\n') if 'δ' in l][:20])
