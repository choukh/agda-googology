# 紧的读法, 极限节点也下降

> 不含记号. 结论写在 [GuardWeak](GuardWeak.lagda.md). 由 [GuardReadRd](GuardReadRd.lagda.md) 取来 (脚本), 只差三处, 都是测试逼出来的 (路径 `p₁`, 与 $\psi_1(1)$ 上的路径):
>
> 1. `xL` 带 `Lk`: 极限节点模 $\approx$ 搬到更低的分支之后, 还是答那个分支. 那里 `rxL` 把它降成 `xC` (不下降).
> 2. `rx` 对节点 0 答第一支 (`zpos`): 节点 0 没有内容, 不用带帧. 那里答 `xC`.
> 3. 规格: `FN`, `fn-rec`, `fn-rx`, `rdV`, `rdΩ₁`: 后继与闭包节点只答第一支或后继分支, 带 `Nw`. 下面的说明来自原文件.
>
> - `Reader G g01 str cnt`: **一个读法.** 输入 $G:\mathsf{Ord}^\mathsf I\to$ 层号 (闭包的分支), 第一支是 $G\,1$. 读 $P\in G\,\eta$: 对 $\eta$ 结构递归. $\eta=b+1$, 问切口 `str`: 落在 $G\,b$ 里就下降, 否则就是分支 $b+1$. $\eta=\lim f$: 由 `cnt` 位置给出 $n$, 下降到 $f\,n$. **不比较分支值, 不判定位置, 除了 [GuardTightRd](GuardTightRd.lagda.md) 同样用的字面上界 (`guard₁`).**
> - `Tc-of`: `Rs x` 与 `Good x` 推出 `Tc (rb₁ x)`. 一个定理, 对层 1 的一切带切口的好项. `Tc-F`: 一切 $\theta$. `Tc-Lv₅`: 第 5 站. 又 `Tc-add`, `Tc-iter`: 字面的闭包也是实例, 不再要 `Tail` 的视图.
> - **模块参数不是假设:** `Reader` 的参数是读法的输入, 实例闭合.
>
> 与 `Tail` 的差别只在 $G\,1$: 这里 $G\,1$ 的位置都读成第一支 (`fst`), 不带帧; `Tail` 把 $G\,1$ 的新节点读成分支 1. 两者的界相同 ($c_2=1$), 比较见 [GuardReadAccept](GuardReadAccept.lagda.md) 的 `agree`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardWeakRd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; _≅ᴵ_; Ordᶜ; Simᴵ; Ω; ψ; add; _+_; _≅_; limᵢ; up; lim; suc; zero; z≅; s≅; l≅; s⊑; z⊑; upˡ; upʳ; ≅ᴵ-refl; ⊑ᴵ-refl; Ω-refl)
open import OCF.Align.GuardTightLv using (Dom₀; module Lv; pr)
module LvD = Lv Dom₀
open LvD using (Src; LG; lc; _≈_; l≈; s≈; o≈; _⊴_; Cp; self; fst; bra; AdmC; ⊴p; ⊴K; viaᴸ; viaᴷ; zero; suc; lim; Cfˢ; ≈-sym)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightRd using (guard₁; guardL)
import OCF.Align.GuardTightUni as Uni
open Uni Dom₀ using (_⊑ᵒ_; ψ¹; F; F-mono; self-F; Lv₅; rb₀; rb₁; em; em-self; em-mono; rb-≈₁₁; Good; good-em; good-F; idO; chain; chain-≅; b0; b1; ⊑ᵒ-≅ʳ; ≅→⊑ᵒ; gz; gs; gl; gi; gu; Good→Gd)
open import OCF.Align.GuardReadCut
open import OCF.Align.GuardReadRs
```

## §1 读法

`NZ b`: $b$ 不是字面的 0. **第 0 步不问切口**: $G\,1$ 就是第一支. 这一步没有内容: 第 5 站上问 $F\,0$ 是不是 $F\,1$ 的切口要比较 $1$ 与下标 $z$ (判断: 退化的 $z=\lim(0,0,\dots)$ 上带不了证据), 也用不着.

`Rx`: 带规格的答案. `xF`: 第一支. `xN b`: 分支 $b+1$, 带 `Nw (G b) rep`: 要么 $G\,b$ 在节点之下 (`Ab`), 要么节点是 0 或极限 (`LZ`). `xL`, `xC`: 只在节点是 0 或极限时 (`LZ k`). **所以后继与闭包节点只有 `xF` 与 `xN`.**

```agda
NZ : Ordᴵ → Set
NZ zero = ⊥
NZ (suc _) = ⊤
NZ (lim _ _) = ⊤

Nw : LG → LG → Set
Nw A k = Ab A k ⊎ LZ k

nz? : ∀ b → (b ≡ zero) ⊎ NZ b
nz? zero = inj₁ refl
nz? (suc _) = inj₂ tt
nz? (lim _ _) = inj₂ tt

lz-lk : ∀ {k rep} → Lk k rep → LZ rep → LZ k
lz-lk {k = zero} d l = tt
lz-lk {k = lim f} d l = tt
lz-lk {k = suc k} (inj₁ (s≈ _)) ()
lz-lk {k = suc k} (inj₂ refl) ()
lz-lk {k = lc c t g} (inj₁ (o≈ _ _ _)) ()
lz-lk {k = lc c t g} (inj₂ refl) ()

-- 后继与闭包节点
NL : LG → Set
NL LvD.zero = ⊥
NL (LvD.suc _) = ⊤
NL (LvD.lim _) = ⊥
NL (lc _ _ _) = ⊤

nl-lk : ∀ {k rep} → Lk k rep → NL k → NL rep
nl-lk (inj₂ refl) n = n
nl-lk {k = LvD.suc _} (inj₁ (s≈ _)) n = tt
nl-lk {k = lc _ _ _} (inj₁ (o≈ _ _ _)) n = tt

nl-lim : ∀ {k f} → Lk k (LvD.lim f) → NL k → ⊥
nl-lim {k = LvD.zero} d n = n
nl-lim {k = LvD.lim _} d n = n
nl-lim {k = LvD.suc _} (inj₁ ()) n
nl-lim {k = LvD.suc _} (inj₂ ()) n
nl-lim {k = lc _ _ _} (inj₁ ()) n
nl-lim {k = lc _ _ _} (inj₂ ()) n

-- 节点 0 的第一位置: 不走分支, 所以不带帧
zpos : ∀ t → Cp zero t
zpos zero = self
zpos (suc b) = suc (zpos b)
zpos (lim f) = lim 0 (zpos (f 0))
zpos (lc c t g) = fst (zpos t)

zadm : ∀ t (E : Src) → AdmC E (zpos t)
zadm zero E = tt
zadm (suc b) E = zadm b E
zadm (lim f) E = zadm (f 0) E
zadm (lc c t g) E = zadm t E

module Reader (G : Ordᴵ → LG)
  (g01 : G zero ⊴ G (suc zero))
  (str : ∀ b → NZ b → ∀ {k} (P : Cp k (G (suc b))) → Cu (G b) P)
  (cnt : ∀ f s → G (lim f s) ≈ lim (λ n → G (f n))) where

  t₁ : LG
  t₁ = G (suc zero)

  g₁ : (η : Ordᴵ) → suc zero ⊑ᴵ η → LG
  g₁ η e = G η

  data Rx (η₀ : Ordᴵ) {x k : LG} (P : Cp k x) : Set where
    xF : ∀ {rep} → Lk k rep → (Q : Cp rep t₁) → (∀ E → AdmC E P → AdmC E Q) → Rx η₀ P
    xN : ∀ {rep} (b : Ordᴵ) → NZ b → (ea : suc zero ⊑ᴵ suc b) → suc b ⊲ η₀ → Lk k rep → (Q : Cp rep (G (suc b))) → (∀ E → AdmC E P → AdmC E Q) → Nw (G b) rep → Rx η₀ P
    xL : ∀ {rep} (a : Ordᴵ) (ea : suc zero ⊑ᴵ a) → a ⊲ η₀ → Lk k rep → (Q : Cp rep (G a)) → (∀ E → AdmC E P → AdmC E Q) → LZ k → Rx η₀ P
    xC : LZ k → Rx η₀ P

  rxT : ∀ {η₀ x x′ k} {P : Cp k x} {P′ : Cp k x′} → (∀ E → AdmC E P → AdmC E P′) → Rx η₀ P′ → Rx η₀ P
  rxT t (xF d Q u) = xF d Q (λ E a → u E (t E a))
  rxT t (xN b nz ea m d Q u w) = xN b nz ea m d Q (λ E a → u E (t E a)) w
  rxT t (xL a ea m d Q u l) = xL a ea m d Q (λ E a → u E (t E a)) l
  rxT t (xC l) = xC l

  rxL : ∀ {η₀ x x′ k rep} {P : Cp k x} {P′ : Cp rep x′} → Lk k rep → (∀ E → AdmC E P → AdmC E P′) → Rx η₀ P′ → Rx η₀ P
  rxL (inj₂ refl) t r = rxT t r
  rxL (inj₁ d) t (xF d′ Q u) = xF (lkT d d′) Q (λ E a → u E (t E a))
  rxL (inj₁ d) t (xN b nz ea m d′ Q u w) = xN b nz ea m (lkT d d′) Q (λ E a → u E (t E a)) w
  rxL {k = k} (inj₁ d) t (xL a ea m d′ Q u l) = xL a ea m (lkT d d′) Q (λ E a → u E (t E a)) (lz-lk (inj₁ d) l)
  rxL (inj₁ d) t (xC l) = xC (lz-lk (inj₁ d) l)

  -- G 0 的位置: 搬到第一支. 只有后继与闭包节点搬得动
  mv₀ : ∀ {η₀ k} (P : Cp k (G zero)) → Rx η₀ P
  mv₀ {k = zero} P = xC tt
  mv₀ {k = lim f} P = xC tt
  mv₀ {k = suc k′} P with ⊴p g01 (fromCpS P)
  ... | viaᴸ d p t = xF (inj₁ (s≈ d)) (toCpS p) (λ E a → admToS p (t E (admFromS P a)))
  mv₀ {k = lc c t g} P with ⊴K g01 P
  ... | viaᴷ d p u = xF (inj₁ d) p u

  module _ (η₀ : Ordᴵ) (z₀ : zero <ᴵ η₀) where
    new : ∀ b (nz : NZ b) {k} (P : Cp k (G (suc b))) → Simᴵ (suc b) η₀ → Nw (G b) k → Rx η₀ P
    new b nz P σ w = xN b nz (guard₁ (σ zero) z₀) (⊲ˢ (λ σ′ → σ′ (σ zero))) (inj₂ refl) P (λ _ a → a) w

    rec : ∀ x {k} (P : Cp k (G x)) → Simᴵ x η₀ → Maybe (x <ᴵ η₀) → Rx η₀ P
    rec zero P σ l = mv₀ P
    rec (suc b) P σ l with nz? b
    rec (suc .zero) P σ l | inj₁ refl = xF (inj₂ refl) P (λ _ a → a)
    rec (suc b) P σ l | inj₂ nz with str b nz P
    ... | cIn d Q u = rxL d u (rec b Q (λ r → σ (suc r)) (just (σ zero)))
    ... | cNw w = new b nz P σ (inj₁ w)
    ... | cUn z = new b nz P σ (inj₂ z)
    rec (lim f s) P σ l with mvC P (cnt f s)
    rec (lim f s) P σ (just q) | mvc d self u = xL (lim f s) (guardL q z₀) (⊲ˢ (λ σ′ → σ′ q)) (inj₂ refl) P (λ _ a → a) (lz-lk d tt)
    rec (lim f s) P σ nothing  | mvc d self u = xC (lz-lk d tt)
    rec (lim f s) P σ l | mvc d (lim n Q) u = rxL d u (rec (f n) Q (λ r → σ (lim n r)) nothing)

  rx : ∀ η (e : suc zero ⊑ᴵ η) {k} (P : Cp k (G η)) → Rx η P
  rx zero (s⊑ _ ()) P
  rx η e {k = zero} P = xF (inj₂ refl) (zpos t₁) (λ E _ → zadm t₁ E)
  rx (suc b) (s⊑ z≅ z₀) {k = suc k′} P = rec (suc b) z₀ (suc b) P (λ r → r) nothing
  rx (suc b) (s⊑ z≅ z₀) {k = lim f′} P = rec (suc b) z₀ (suc b) P (λ r → r) nothing
  rx (suc b) (s⊑ z≅ z₀) {k = lc c′ t′ g′} P = rec (suc b) z₀ (suc b) P (λ r → r) nothing
  rx (lim f s) (s⊑ z≅ z₀) {k = suc k′} P = rec (lim f s) z₀ (lim f s) P (λ r → r) nothing
  rx (lim f s) (s⊑ z≅ z₀) {k = lim f′} P = rec (lim f s) z₀ (lim f s) P (λ r → r) nothing
  rx (lim f s) (s⊑ z≅ z₀) {k = lc c′ t′ g′} P = rec (lim f s) z₀ (lim f s) P (λ r → r) nothing

  -- 规格: 后继与闭包节点只有 xF 与 xN, 所以规范位置上的分支值是后继
  data FN {η₀ x k} {P : Cp k x} : Rx η₀ P → Set where
    fnF : ∀ {rep} {d : Lk k rep} {Q : Cp rep t₁} {u} → FN (xF d Q u)
    fnN : ∀ {rep b nz ea m} {d : Lk k rep} {Q : Cp rep (G (suc b))} {u w} → FN (xN b nz ea m d Q u w)

  fn-rxT : ∀ {η₀ x x′ k} {P : Cp k x} {P′ : Cp k x′} (t : ∀ E → AdmC E P → AdmC E P′) (r : Rx η₀ P′) → FN r → FN (rxT {P = P} t r)
  fn-rxT t _ fnF = fnF
  fn-rxT t _ fnN = fnN

  fn-rxL : ∀ {η₀ x x′ k rep} {P : Cp k x} {P′ : Cp rep x′} (d : Lk k rep) (t : ∀ E → AdmC E P → AdmC E P′) (r : Rx η₀ P′) → FN r → FN (rxL {P = P} d t r)
  fn-rxL (inj₂ refl) t r h = fn-rxT t r h
  fn-rxL (inj₁ d) t _ fnF = fnF
  fn-rxL (inj₁ d) t _ fnN = fnN

  module _ (η₀ : Ordᴵ) (z₀ : zero <ᴵ η₀) where
    fn-rec : ∀ x {k} → NL k → (P : Cp k (G x)) (σ : Simᴵ x η₀) (l : Maybe (x <ᴵ η₀)) → FN (rec η₀ z₀ x P σ l)
    fn-rec zero {suc k′} n P σ l with ⊴p g01 (fromCpS P)
    ... | viaᴸ d p t = fnF
    fn-rec zero {lc c t g} n P σ l with ⊴K g01 P
    ... | viaᴷ d p u = fnF
    fn-rec (suc b) n P σ l with nz? b
    fn-rec (suc .zero) n P σ l | inj₁ refl = fnF
    fn-rec (suc b) n P σ l | inj₂ nz with str b nz P
    ... | cIn d Q u = fn-rxL d u _ (fn-rec b (nl-lk d n) Q (λ r → σ (suc r)) (just (σ zero)))
    ... | cNw w = fnN
    ... | cUn z = fnN
    fn-rec (lim f s) n P σ l with mvC P (cnt f s)
    fn-rec (lim f s) n P σ (just q) | mvc d self u = ⊥-elim (nl-lim d n)
    fn-rec (lim f s) n P σ nothing  | mvc d self u = ⊥-elim (nl-lim d n)
    fn-rec (lim f s) n P σ l | mvc d (lim n′ Q) u = fn-rxL d u _ (fn-rec (f n′) (nl-lk d n) Q (λ r → σ (lim n′ r)) nothing)

  fn-rx : ∀ η (e : suc zero ⊑ᴵ η) {k} → NL k → (P : Cp k (G η)) → FN (rx η e P)
  fn-rx zero (s⊑ _ ()) n P
  fn-rx (suc b) (s⊑ z≅ z₀) {k = suc k′} n P = fn-rec (suc b) z₀ (suc b) n P (λ r → r) nothing
  fn-rx (suc b) (s⊑ z≅ z₀) {k = lc c′ t′ g′} n P = fn-rec (suc b) z₀ (suc b) n P (λ r → r) nothing
  fn-rx (lim f s) (s⊑ z≅ z₀) {k = suc k′} n P = fn-rec (lim f s) z₀ (lim f s) n P (λ r → r) nothing
  fn-rx (lim f s) (s⊑ z≅ z₀) {k = lc c′ t′ g′} n P = fn-rec (lim f s) z₀ (lim f s) n P (λ r → r) nothing

  toRd : ∀ {η e k} {P : Cp k (G η)} → Rx η P → RdO (suc zero) t₁ g₁ η e P
  toRd (xF d Q u) = rdF d Q u
  toRd (xN b nz ea m d Q u w) = rdB (suc b) ea m d Q u
  toRd (xL a ea m d Q u l) = rdB a ea m d Q u
  toRd {η} {e} {P = P} (xC l) = rdB η e ⊲= (inj₂ refl) P (λ _ a → a)

  rdU : Rdr (suc zero) t₁ g₁
  rdU η e P = toRd (rx η e P)
```

## §2 一个定理: 带切口的项有读法

```agda
tc-rb₀ : ∀ (x : Ordᶜ zero) → Tc (rb₀ x)
tc-rb₀ zero = tt
tc-rb₀ (suc x) = tc-rb₀ x
tc-rb₀ (lim f) = λ n → tc-rb₀ (f n)
tc-rb₀ (limᵢ () f)
tc-rb₀ (up () x)

-- 闭包 limᵢ zero f 的读法: G η = rb₁ (f (em η))
-- 读位置的回答 (规格): 第一支, 或后继分支, 带 Nw
data RdV (G′ : Ordᴵ → LG) {c t g η e k} {P : Cp k (g η e)} : RdO c t g η e P → Set where
  rvF : ∀ {rep} {d : Lk k rep} {Q : Cp rep t} {tr} → RdV G′ (rdF d Q tr)
  rvN : ∀ {rep} b {ea : c ⊑ᴵ suc b} {l} {d : Lk k rep} {Q : Cp rep (g (suc b) ea)} {tr} → Nw (G′ b) rep → RdV G′ (rdB (suc b) ea l d Q tr)

module OfF (f : Ordᶜ zero → Ordᶜ (suc zero))
           (hm : ∀ {z z′ : Ordᶜ zero} → z ⊑ᵒ z′ → f z ⊑ᵒ f z′)
           (st : ∀ (z : Ordᶜ zero) → z ≅ z → Sp (f z) (f (suc z)))
           (ct : ∀ (h : ℕ → Ordᶜ zero) → (∀ n → h n ≅ h n) → f (lim h) ≅ lim (λ n → f (h n))) where
  G : Ordᴵ → LG
  G η = rb₁ (f (em η))

  open Reader G (hm (em-mono z⊑) (idO {b = b1} {b′ = b1}))
              (λ b nz P → read b1 b1 (st (em b) (em-self b)) P)
              (λ g s → rb-≈₁₁ (ct (λ n → em (g n)) (λ n → em-self (g n)))) public

  rdV : ∀ η e {k} → NL k → (P : Cp k (G η)) → RdV G (rdU η e P)
  rdV η e n P with rx η e P | fn-rx η e n P
  ... | xF d Q u | fnF = rvF
  ... | xN b nz ea m d Q u w | fnN = rvN b w

Tc-of : ∀ {x : Ordᶜ (suc zero)} → Rs x → Good x → Tc (rb₁ x)
Tc-of rz gz = tt
Tc-of (rs g) (gs g′) = Tc-of g g′
Tc-of (rl h) (gl h′ _) = λ n → Tc-of (h n) (h′ n)
Tc-of (ri {p = zero} {f = f} hb st ct) (gi hb′ hm) =
  OfF.rdU f hm st ct ,
  Tc-of (hb (suc zero) (s≅ z≅) (rs rz)) (hb′ (suc zero) (s≅ z≅) (gs gz)) ,
  (λ η e → Tc-of (hb (em η) (em-self η) (Rs-em η)) (hb′ (em η) (em-self η) (good-em η)))
Tc-of (ri {p = suc ()} hb st ct) _
Tc-of (ru {r = zero} {x = x} g) _ = tc-rb₀ x
```

## §3 $F\,\theta$ 与 $\mathrm{Lv}_5$

`Tc-F`: **对一切 $\theta$.** `sp-F`: $F\,b$ 是 $F(b+1)$ 的切口, $b$ 不是字面 0. $F(b+1)$ 是 $\lim_n\psi_1(x_n)$, $x_0=\Omega_b$, $x_{n+1}=\psi_b(x_n)$. $\Omega_b$ 是每个 $x_n$ 的切口 (`sp-Ωψ`), $\psi_1$ 保持切口 (`Sp-ψ¹`). **第 5 站没有定制的东西**: 只比 `Tc-of` 多这一条, 因为 `Lv₅` 的下标是 `Ordᴵ`, 不在 `limᵢ` 里.

```agda
Tc-F : ∀ θ → Tc (F θ)
Tc-F θ = Tc-of (Rs-ψ¹ (Rs-Ω θ) (Ω-refl θ)) (good-F θ)

sp-ch : ∀ j n → Sp (Ω j) (chain {j} {suc j} zero (up zero) n)
sp-ch j zero = s-eq (Ω-refl j)
sp-ch j (suc n) = sp-Ωψ {q = zero} {σ = λ r → r} (up zero (chain zero (up zero) n)) (upˡ (upʳ (chain-≅ (Ω-refl (suc j)) n)))

sp-F : ∀ b → NZ b → Sp (ψ¹ (Ω b)) (ψ¹ (Ω (suc b)))
sp-F (suc c) _ = s-lim (λ n → Sp-ψ¹ (Ω-refl (suc c)) (sp-ch (suc c) n))
sp-F (lim g s) _ = s-lim (λ n → Sp-ψ¹ (Ω-refl (lim g s)) (sp-ch (lim g s) n))

module RdLv₅ = Reader F (F-mono z⊑) (λ b nz P → read b1 b1 (sp-F b nz) P) (λ g s → l≈ (λ n → self-F (g n)))

Tc-Lv₅ : Tc Lv₅
Tc-Lv₅ = RdLv₅.rdU , Tc-F (suc zero) , (λ η e → Tc-F η)
```

## §4 字面的闭包也是实例

$\Omega_1$, $a+\Omega_1$, $\Omega_1\cdot n$: 不要 `Tail` 的视图, 不要 `RdAdd`, `RdIter`.

```agda
Tc-Ω₁ : Tc (rb₁ (Ω (suc zero)))
Tc-Ω₁ = Tc-of (Rs-Ω (suc zero)) (Uni.Good-Ω Dom₀ (suc zero))

rdΩ₁ : ∀ η e {k} → NL k → (P : Cp k (rb₁ (up zero (em η)))) → RdV (λ b → rb₁ (up zero (em b))) (proj₁ Tc-Ω₁ η e P)
rdΩ₁ η e n P = OfF.rdV (up zero) (λ h → Uni.up-l Dom₀ (Uni.up-r Dom₀ h))
                       (λ z ez → s-up (s-suc (Uni.up-l Dom₀ (Uni.≅→⊑ᵒ Dom₀ ez)) ez (s-eq (upˡ ez))))
                       (λ h he → upˡ (l≅ (λ n → upʳ (he n)))) η e n P

Tc-add : ∀ {a b : Ordᶜ (suc zero)} → Rs a → Good a → a ≅ a → Rs b → Good b → b ≅ b → Tc (rb₁ (a + b))
Tc-add ra ga ea rb gb eb = Tc-of (Rs-add ra ea rb eb) (Uni.Good-add Dom₀ {σ = λ q → q} ga ea gb)

Tc-iter : ∀ n → Tc (rb₁ (iter (Ω (suc zero) +_) zero n))
Tc-iter n = Tc-of (Rs-iter (Rs-Ω (suc zero)) (Ω-refl (suc zero)) n) (Uni.Good-iter Dom₀ (Uni.Good-Ω Dom₀ (suc zero)) (Ω-refl (suc zero)) n)
```
