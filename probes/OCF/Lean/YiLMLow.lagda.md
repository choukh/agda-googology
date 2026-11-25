# 验收一侧: ω 层 (`lim fin`) 上的关系, `Leaf`, 折到有限层的保持

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `Mω` 是 `YiMEBase.Mᴰ` 在层号 `lim fin` 上的实例 (槽位 (m, t) 的分支关系是 `Lw m t`, 第 m 个孩子的关系是 `M m`); `leafω`: 第 ω 层的 Ω 树对着 Ω_ω.
> `LFω`: 主线折叠把 `Mω a x` 送到 `M j (ψ_j(t₀ + a))`, 对一切推导 (含 `mw`) 与一切有限的 j. 量化域收窄在三处, 都不在树 x 上: 路线取相邻一步 `R₀`, 路径取 `inl n (pthᶠ s)`, 底满足 `GBω` (标准底满足: `gbω₀`).
> 不涉及一般的 `lim g`, Ω 形状层号, 上界, 折到 ω 层自身; 不涉及把第 0 层的树读成层号 (`YiCLCrit.no-least` 说的是那一处). 接口上的陈述与检验见 [YiLMCheck](YiLMCheck.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLMLow where

open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
import OCF.Lean.YiLegPath as P
open P using (_≤_; self; ins; inl; _∙_; posW; psh; pshBr; Ev; Rt; Adj; Way; fwd; bwd; caseW; way; way′; rt; _<ₙ_; emb)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSFold using (ψs-⊵)
import OCF.Align.EboLeanDef as E
open E using (cof; cω; cΩ; fsn; fsT; γT; ψ; 𝟏; natT)
open import OCF.Lean.YiMEBase hiding (Rt)
open import OCF.Lean.YiMENote
open import OCF.Lean.YiMEAnchor using (++[]; Qu)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiEVReach using (cv⊴)
open import OCF.Lean.YiANFam
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss; pthᶠ; GBᶠ; mkGBᶠ)
open import OCF.Lean.YiASProofLow
open import OCF.Lean.YiASProofMin using (mΩt)
```

## ω 层的关系与 `Leaf`

层号 `lim fin` 的槽位 (m, t) 与层号 `fin (suc m)` 的槽位 t 有同一个分支类型, 关系与允许的余尾下标照抄. 参照 Ω_ω = ψ_ω(0), ω = ψ₀(1); 它的基本列第 n 项是 Ω_n.
Ω 树是 Ω_0 + … + Ω_n 的极限; 每个 Ω_n 由 "零加第 n 个孩子" 对上, 所以 `Leaf` 在未封闭的 `Mω` 上成立.

```agda
ωL : L
ωL = lim fin

ωᵀ Ωω : E.T
ωᵀ = ψ [] (𝟏 ∷ []) ∷ []
Ωω = ψ ωᵀ [] ∷ []

Mω : E.T → Tr ωL → Set
Mω = Mᴰ (Sig ωL) (λ p → Lw (proj₁ p) (proj₂ p)) (λ m → M m) (λ p → Nw (proj₁ p) (proj₂ p))

rep𝟏 : ∀ n → replicate n 𝟏 ≡ natT n
rep𝟏 zero    = refl
rep𝟏 (suc n) = cong (𝟏 ∷_) (rep𝟏 n)

cumM : ∀ n → Mω (Ωᴺ n) (cumΩ fin n)
cumM zero    = mU mz (mΩt 0)
cumM (suc n) = mU mz (mΩt (suc n))

leafω : Mω Ωω (Ωt ωL)
leafω = mL refl (λ n → subst (λ u → Mω (ψ u [] ∷ []) (Ωt ωL)) (sym (rep𝟏 n)) (mw (cumM n) (◃l n)))
```

## 量化域: 路线, 路径, 底

路线 `R₀`: 相邻孩子之间走一步 `ins self`. 于是孩子之间的路径都是 `pthᶠ` (`wv`), 复合仍是 `pthᶠ` (`∙≡`).
`GBω B t₀`: 底在每条路径 `inl m (pthᶠ si)` 上的分量在 Ω 树之上, 且对着 ψ_i(t₀) (`YiASIface.GBᶠ` 的对应物).

```agda
R₀ : Adj fin
R₀ n = ins self

record GBω (B : Base ωL) (t₀ : E.T) : Set where
  constructor mkGBω
  field
    wΩ : ∀ m {i} (si : Sbᶠ m i) → Ωt (fin i) ⊴ bs B (fin i) (inl m (pthᶠ si))
    wM : ∀ m {i} (si : Sbᶠ m i) → M i (ψᴺ i t₀) (bs B (fin i) (inl m (pthᶠ si)))
open GBω public

gbω₀ : GBω (B₀ ωL) []
gbω₀ = mkGBω (λ m si → ⊴r) (λ m {i} si → mΩt i)

comp : ∀ {n j m} → Sbᶠ n j → Sbᶠ m n → Sbᶠ m j
comp s s0      = s
comp s (ss s′) = ss (comp s s′)

∙≡ : ∀ {n j m} (s : Sbᶠ n j) (s′ : Sbᶠ m n) → pthᶠ s ∙ pthᶠ s′ ≡ pthᶠ (comp s s′)
∙≡ s s0      = refl
∙≡ s (ss s′) = cong ins (∙≡ s s′)

sl : ∀ {m n} → m <ₙ n → Sbᶠ n m
sl P.here    = ss s0
sl (P.nxt l) = ss (sl l)

rt≡ : ∀ {m n} (l : m <ₙ n) → rt fin R₀ l ≡ pthᶠ (sl l)
rt≡ P.here    = refl
rt≡ (P.nxt l) = cong ins (rt≡ l)

data WV (m : ℕ) : (n : ℕ) → Way fin m n → Set where
  wf : ∀ {n} (s′ : Sbᶠ n m) → WV m (suc n) (fwd (ins (pthᶠ s′)))
  wb : ∀ {n} (s′ : Sbᶠ m n) → WV m n (bwd (pthᶠ s′))

wv′ : ∀ {m n} (c : P.Cmp m n) → WV m n (way′ fin R₀ c)
wv′ P.eq               = wb s0
wv′ (P.lt P.here)      = wf s0
wv′ {m} (P.lt (P.nxt {n} l)) = subst (λ v → WV m (suc n) (fwd (ins v))) (sym (rt≡ l)) (wf (sl l))
wv′ {m} {n} (P.gt l)   = subst (λ v → WV m n (bwd v)) (sym (rt≡ l)) (wb (sl l))

wv : ∀ m n → WV m n (way fin R₀ m n)
wv m n = wv′ (P.cmp m n)
```

## 有限层上的合并形式, 孩子树的搬运

`LFA`: `YiASProofLow.LFᶠ`, `YiANFam.Self.PF`, `YiMEAnchor.Qu` 按路径合成一条 (第 0 层只有 `self`).

```agda
GBᴬ′ : (m : ℕ) → Base (fin m) → E.T → Set
GBᴬ′ zero    B t₀ = ⊤
GBᴬ′ (suc m) B t₀ = GBᶠ m B t₀

LFA : ∀ {m j} (s : Sbᶠ m j) (t₀ : E.T) (ε : Ev (fin m)) (ρ : Rt (fin m)) (B : Base (fin m))
    → GBᴬ′ m B t₀ → (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) → M j (ψᴺ j t₀) β
    → ∀ {a x} → M m a x → M j (ψᴺ j (t₀ ++ a)) (ψs (fin m) ε ρ B (fin j) (pthᶠ s) β nβ x)
LFA {m = zero}  s0     t₀ ε ρ B gb β nβ hβ r = Qu B β nβ hβ r
LFA {m = suc m} s0     t₀ ε ρ B gb β nβ hβ r = Self.PF m ε ρ B β nβ hβ r
LFA {m = suc m} (ss s) t₀ ε ρ B gb β nβ hβ r = LFᶠ s t₀ ε ρ B gb β nβ hβ r

embM : ∀ {n m} (s′ : Sbᶠ n m) (ε : Ev (fin n)) (y : Tr (fin m)) (ey : fin m ⊢ zero ◃ y) {s₁}
     → M m s₁ y → M n s₁ (emb (fin n) ε (pthᶠ s′) y ey)
embM s0      ε y ey ch = ch
embM (ss s′) ε y ey ch = mU mz (embM s′ ε y ey ch)
```

## 保留判定

槽位 (m, `pos⁼ si`) (槽位层 i) 朝目标 `fin j` (路径 `inl n (pthᶠ s)`): 与有限层号同一个判定, j ≤ i 时不保留, 否则保留.
m < n 时槽位先沿路径搬进孩子 n (`kcaseF`), 否则目标路径接到孩子 m 上 (`YiASProofLow.kcase`).

```agda
slotPsh : ∀ {n m} (s′ : Sbᶠ n m) (t : Pos⁼ (fin m)) → slot n (psh (pthᶠ s′) t) ≡ slot m t
slotPsh s0      t = refl
slotPsh (ss s′) t = slotPsh s′ t

lwPsh : ∀ {n m} (s′ : Sbᶠ n m) (t : Pos⁼ (fin m)) {η} (c : Br⁼ (fin n) (psh (pthᶠ s′) t))
      → Lw n (psh (pthᶠ s′) t) η c → Lw m t η (pshBr (pthᶠ s′) t c)
lwPsh s0      t c l = l
lwPsh (ss s′) t c l = lwPsh s′ t c l

kcaseF : ∀ {n m i j} (s′ : Sbᶠ n m) (si : Sbᶠ m i) (s : Sbᶠ n j) (ε : Ev (fin n)) (ρ : Rt (fin n)) {X : Set} (Q : X → Set)
         {K : (q : Pos (fin j)) → (Br (fin j) q → Br⁼ (fin n) (psh (pthᶠ s′) (pos⁼ si))) → X} {d : X}
       → (j ≤ⁿ i → Q d)
       → ((q : Pos (fin j)) (cv : Br (fin j) q → Br⁼ (fin n) (psh (pthᶠ s′) (pos⁼ si))) → levP j q ≡ i
            → (∀ η c → LwP j q η c → Lw m (pos⁼ si) η (pshBr (pthᶠ s′) (pos⁼ si) (cv c))) → Q (K q cv))
       → Q (kp⁼ (fin n) ε ρ (psh (pthᶠ s′) (pos⁼ si)) (pthᶠ s) K d)
kcaseF s0      si s      ε ρ Q dr kc = kcase si s ε ρ Q dr kc
kcaseF (ss s′) si s0     ε ρ Q dr kc =
  kc (psh (pthᶠ s′) (pos⁼ si)) (λ z → z) (trans (slotPsh s′ (pos⁼ si)) (levEq si)) (λ η c l → lwPsh s′ (pos⁼ si) c l)
kcaseF (ss s′) si (ss s) ε ρ Q dr kc = kcaseF s′ si s ε ρ Q dr kc

kcW : ∀ {m n i j} (si : Sbᶠ m i) (s : Sbᶠ n j) (ε : Ev ωL) (ρc : (k : ℕ) → Rt (fin k)) {X : Set} (Q : X → Set)
      {K : (q : Pos (fin j)) → (Br (fin j) q → Br⁼ (fin m) (pos⁼ si)) → X} {d : X}
    → (j ≤ⁿ i → Q d)
    → ((q : Pos (fin j)) (cv : Br (fin j) q → Br⁼ (fin m) (pos⁼ si)) → levP j q ≡ i
         → (∀ η c → LwP j q η c → Lw m (pos⁼ si) η (cv c)) → Q (K q cv))
    → (W : Way fin m n) → WV m n W
    → Q (caseW W (λ v → kp⁼ (fin n) (ε n) (ρc n) (psh v (pos⁼ si)) (pthᶠ s) (λ q cv → K q (λ z → pshBr v (pos⁼ si) (cv z))) d)
                 (λ v → kp⁼ (fin m) (ε m) (ρc m) (pos⁼ si) (pthᶠ s ∙ v) K d))
kcW si s ε ρc Q {K} {d} dr kc _ (wf s′) =
  kcaseF (ss s′) si s (ε _) (ρc _) Q {K = λ q cv → K q (λ z → pshBr (ins (pthᶠ s′)) (pos⁼ si) (cv z))} {d = d} dr
    (λ q cv lq lw → kc q (λ z → pshBr (ins (pthᶠ s′)) (pos⁼ si) (cv z)) lq lw)
kcW {m = m} si s ε ρc Q {K} {d} dr kc _ (wb s′) =
  subst (λ w → Q (kp⁼ (fin m) (ε m) (ρc m) (pos⁼ si) w K d)) (sym (∙≡ s s′))
    (kcase si (comp s s′) (ε m) (ρc m) Q dr kc)

kcaseω : ∀ {m n i j} (si : Sbᶠ m i) (s : Sbᶠ n j) (ε : Ev ωL) (ρc : (k : ℕ) → Rt (fin k)) {X : Set} (Q : X → Set)
         {K : (q : Pos (fin j)) → (Br (fin j) q → Br⁼ (fin m) (pos⁼ si)) → X} {d : X}
       → (j ≤ⁿ i → Q d)
       → ((q : Pos (fin j)) (cv : Br (fin j) q → Br⁼ (fin m) (pos⁼ si)) → levP j q ≡ i
            → (∀ η c → LwP j q η c → Lw m (pos⁼ si) η (cv c)) → Q (K q cv))
       → Q (kp ωL ε (ρc , R₀) (m , pos⁼ si) (inl n (pthᶠ s)) K d)
kcaseω {m} {n} si s ε ρc Q dr kc = kcW si s ε ρc Q dr kc (way fin R₀ m n) (wv m n)
```

## 折叠的缩写, 回灌

`Fω s …` 是朝 `fin j` 沿 `inl n (pthᶠ s)` 的折叠. `vchω` 逐字是折叠在结点一行里的回灌链; 它的每一步是朝槽位层 `fin i` 沿 `inl m (pthᶠ si)` 的折叠 (`feed≡ω`).

```agda
module _ (ε : Ev ωL) (ρc : (k : ℕ) → Rt (fin k)) (B : Base ωL) where

  Fω : ∀ {n j} (s : Sbᶠ n j) (β : Tr (fin j)) → fin j ⊢ zero ◃ β → Tr ωL → Tr (fin j)
  Fω {n} {j} s β nβ x = ψs ωL ε (ρc , R₀) B (fin j) (inl n (pthᶠ s)) β nβ x

  nzFω : ∀ {n j} (s : Sbᶠ n j) (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) (x : Tr ωL) → fin j ⊢ zero ◃ Fω s β nβ x
  nzFω {n} {j} s β nβ x = nzs ωL ε (ρc , R₀) B (fin j) (inl n (pthᶠ s)) β nβ x

  monoFω : ∀ {n j} (s : Sbᶠ n j) (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) {x y : Tr ωL}
         → ωL ⊢ x ◃ y → fin j ⊢ Fω s β nβ x ◃ Fω s β nβ y
  monoFω {n} {j} s β nβ = monos ωL ε (ρc , R₀) B (fin j) (inl n (pthᶠ s)) β nβ

  foω : (p : Pos ωL) → Tr ωL → Tr (at ωL p)
  foω p V = ψs ωL ε (ρc , R₀) B (at ωL p) (posW ωL p) (bs B (at ωL p) (posW ωL p)) (ns B (at ωL p) (posW ωL p)) V

  vchω : (p : Pos ωL) (G : Br ωL p → Tr ωL) → ℕ → Br ωL p
  vchω p G = iter (λ z → fromBr ωL p (foω p (G z))) (br0 ωL p)

  feed≡ω : ∀ {m i} (si : Sbᶠ m i) (x : Tr ωL)
         → fromBr ωL (m , pos⁼ si) (foω (m , pos⁼ si) x)
         ≡ toBr si (Fω si (bs B (fin i) (inl m (pthᶠ si))) (ns B (fin i) (inl m (pthᶠ si))) x)
  feed≡ω {m} si x = gen si (λ k w → ψs ωL ε (ρc , R₀) B k (inl m w) (bs B k (inl m w)) (ns B k (inl m w)) x)
```

## 折到有限层

对 `Mω a x` 的推导归纳, 各行与 `YiASProofLow.LFᶠ` 同形. 嵌入一行 (`LFU`): 孩子 m 的树, m < n 时搬进孩子 n 再用 `LFA`, 否则在孩子 m 上用 `LFA`; 孩子层的底满足 `GBᴬ′` (`gbL`, 用到对 x 的归纳假设).

```agda
mutual
  LFω : ∀ {n j} (s : Sbᶠ n j) (t₀ : E.T) (ε : Ev ωL) (ρc : (k : ℕ) → Rt (fin k)) (B : Base ωL)
      → GBω B t₀ → (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) → M j (ψᴺ j t₀) β
      → ∀ {a x} → Mω a x → M j (ψᴺ j (t₀ ++ a)) (Fω ε ρc B s β nβ x)
  LFω {j = j} s t₀ ε ρc B gb β nβ hβ (mz {x = x}) =
    ++[] (λ r → M j (ψᴺ j r) (Fω ε ρc B s β nβ x)) t₀
      (zlJ j (Fω ε ρc B s β nβ) (monoFω ε ρc B s β nβ) hβ x)
  LFω {j = j} s t₀ ε ρc B gb β nβ hβ (m1 {t = a} {x = x} e r) =
    nextJ j (nzFω ε ρc B s β nβ x) (cofψ1 (natT j) (t₀ ++ a) (cof++1 t₀ a e))
      (λ k → trans (fsnψ1 (natT j) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ r → replicate k (ψ (natT j) r)) (pred++ t₀ a e)))
      (LFω s t₀ ε ρc B gb β nβ hβ r)
  LFω {j = j} s t₀ ε ρc B gb β nβ hβ (mL {t = a} {x = x} e h) =
    mLN j (cofψω (natT j) (t₀ ++ a) (cof++ω t₀ a e))
      (λ k → subst (λ r → M j r (Fω ε ρc B s β nβ x))
        (sym (trans (fsnψω (natT j) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ j) (fsn++ t₀ a k e))))
        (LFω s t₀ ε ρc B gb β nβ hβ (h k)))
  LFω s t₀ ε ρc B gb β nβ hβ (mΩ {p = m , t} e nu h) = LFΩω s t₀ ε ρc B gb β nβ hβ m t (view m t) e nu h
  LFω {n = n} {j = j} s t₀ ε ρc B gb β nβ hβ (mU {t = a} {s = s₁} {x = x} {c = m} {y = y} {e = ey} r ch) =
    subst (λ z → M j (ψᴺ j z) (Fω ε ρc B s β nβ (up x m y ey))) (++-assoc t₀ a s₁)
      (LFU s t₀ ε ρc B gb β nβ hβ m y ey r ch (way fin R₀ m n) (wv m n))
  LFω {j = j} s t₀ ε ρc B gb β nβ hβ (mw r d) =
    mwN j (LFω s t₀ ε ρc B gb β nβ hβ r) (monoFω ε ρc B s β nβ d)

  gbL : ∀ m (t₀ : E.T) (ε : Ev ωL) (ρc : (k : ℕ) → Rt (fin k)) (B : Base ωL) → GBω B t₀
      → ∀ {a x} → Mω a x → GBᴬ′ m (dL fin ε (ρc , R₀) B m x) (t₀ ++ a)
  gbL zero    t₀ ε ρc B gb r = tt
  gbL (suc m) t₀ ε ρc B gb {x = x} r =
    mkGBᶠ (λ {i} si → ⊴-trans (wΩ gb (suc m) (ss si))
             (cv⊴ (ψs-⊵ ωL ε (ρc , R₀) B (fin i) (inl (suc m) (ins (pthᶠ si)))
                     (bs B (fin i) (inl (suc m) (ins (pthᶠ si)))) (ns B (fin i) (inl (suc m) (ins (pthᶠ si)))) x)))
          (λ {i} si → LFω (ss si) t₀ ε ρc B gb (bs B (fin i) (inl (suc m) (ins (pthᶠ si))))
                        (ns B (fin i) (inl (suc m) (ins (pthᶠ si)))) (wM gb (suc m) (ss si)) r)

  LFU : ∀ {n j} (s : Sbᶠ n j) (t₀ : E.T) (ε : Ev ωL) (ρc : (k : ℕ) → Rt (fin k)) (B : Base ωL)
      → GBω B t₀ → (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) → M j (ψᴺ j t₀) β
      → ∀ {a s₁ x} (m : ℕ) (y : Tr (fin m)) (ey : fin m ⊢ zero ◃ y) → Mω a x → M m s₁ y
      → (W : Way fin m n) → WV m n W
      → M j (ψᴺ j ((t₀ ++ a) ++ s₁))
          (caseW W
            (λ v → ψs (fin n) (ε n) (ρc n) (dL fin ε (ρc , R₀) B n x) (fin j) (pthᶠ s)
                     (Fω ε ρc B s β nβ x) (nzFω ε ρc B s β nβ x) (emb (fin n) (ε n) v y ey))
            (λ v → ψs (fin m) (ε m) (ρc m) (dL fin ε (ρc , R₀) B m x) (fin j) (pthᶠ s ∙ v)
                     (Fω ε ρc B s β nβ x) (nzFω ε ρc B s β nβ x) y))
  LFU s t₀ ε ρc B gb β nβ hβ {a} {x = x} m y ey r ch _ (wf {n} s′) =
    LFA s (t₀ ++ a) (ε (suc n)) (ρc (suc n)) (dL fin ε (ρc , R₀) B (suc n) x) (gbL (suc n) t₀ ε ρc B gb r)
      (Fω ε ρc B s β nβ x) (nzFω ε ρc B s β nβ x) (LFω s t₀ ε ρc B gb β nβ hβ r)
      (embM (ss s′) (ε (suc n)) y ey ch)
  LFU {j = j} s t₀ ε ρc B gb β nβ hβ {a} {s₁} {x} m y ey r ch _ (wb s′) =
    subst (λ w → M j (ψᴺ j ((t₀ ++ a) ++ s₁))
                   (ψs (fin m) (ε m) (ρc m) (dL fin ε (ρc , R₀) B m x) (fin j) w (Fω ε ρc B s β nβ x) (nzFω ε ρc B s β nβ x) y))
      (sym (∙≡ s s′))
      (LFA (comp s s′) (t₀ ++ a) (ε m) (ρc m) (dL fin ε (ρc , R₀) B m x) (gbL m t₀ ε ρc B gb r)
        (Fω ε ρc B s β nβ x) (nzFω ε ρc B s β nβ x) (LFω s t₀ ε ρc B gb β nβ hβ r) ch)

  LFΩω : ∀ {n j} (s : Sbᶠ n j) (t₀ : E.T) (ε : Ev ωL) (ρc : (k : ℕ) → Rt (fin k)) (B : Base ωL)
       → GBω B t₀ → (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) → M j (ψᴺ j t₀) β
       → (m : ℕ) (t : Pos⁼ (fin m)) → PV m t → ∀ {a ν} {g : Br⁼ (fin m) t → Tr ωL}
       → cof a ≡ cΩ ν → Nw m t ν → (∀ η c → Lw m t η c → Mω (fsT a η) (g c))
       → M j (ψᴺ j (t₀ ++ a)) (Fω ε ρc B s β nβ (Ω (m , t) g))
  LFΩω {j = j} s t₀ ε ρc B gb β nβ hβ m .(pos⁼ si) (pv {i} si) {a} {ν} {g} e nu h =
    kcaseω si s ε ρc (λ Z → M j (ψᴺ j (t₀ ++ a)) Z)
      (λ le → mLN j (cofG (natT j) (t₀ ++ a) (gtJ le eqν) (cof++Ω t₀ a e))
        (λ k → subst (λ r → M j r (limc (λ k′ → Fω ε ρc B s β nβ (g (vchω ε ρc B (m , pos⁼ si) g k′)))
                                        (λ k′ → nzFω ε ρc B s β nβ (g (vchω ε ρc B (m , pos⁼ si) g k′)))))
          (sym (trans (fsnG (natT j) (t₀ ++ a) k (gtJ le eqν) (cof++Ω t₀ a e))
                      (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
          (cumN j (λ k′ → Fω ε ρc B s β nβ (g (vchω ε ρc B (m , pos⁼ si) g k′)))
                  (λ k′ → nzFω ε ρc B s β nβ (g (vchω ε ρc B (m , pos⁼ si) g k′))) (suc k)
            (LFω s t₀ ε ρc B gb β nβ hβ
              (h (γT (t₀ ++ a) ν k) (vchω ε ρc B (m , pos⁼ si) g (suc k)) (chainω si t₀ ε ρc B gb e eqν h k))))))
      (λ q cv lq lw →
        mΩP j (cofK (natT j) (t₀ ++ a) (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (nuq lq)
          (λ η c l → subst (λ r → M j r (Fω ε ρc B s β nβ (g (cv c))))
            (sym (trans (fsTK (natT j) (t₀ ++ a) η (penJ j q (nuq lq)) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a η e))))
            (LFω s t₀ ε ρc B gb β nβ hβ (h η (cv c) (lw η c l)))))
    where
    eqν : ν ≡ natT i
    eqν = trans nu (cong natT (levEq si))
    nuq : ∀ {q : Pos (fin j)} → levP j q ≡ i → ν ≡ natT (levP j q)
    nuq lq = trans eqν (cong natT (sym lq))

  chainω : ∀ {m i} (si : Sbᶠ m i) (t₀ : E.T) (ε : Ev ωL) (ρc : (k : ℕ) → Rt (fin k)) (B : Base ωL)
         → GBω B t₀ → ∀ {a ν} {g : Br⁼ (fin m) (pos⁼ si) → Tr ωL} → cof a ≡ cΩ ν → ν ≡ natT i
         → (∀ η c → Lw m (pos⁼ si) η c → Mω (fsT a η) (g c))
         → ∀ k → Lw m (pos⁼ si) (γT (t₀ ++ a) ν k) (vchω ε ρc B (m , pos⁼ si) g (suc k))
  chainω {m} {i} si t₀ ε ρc B gb {a} {g = g} e refl h zero =
    subst (Lw m (pos⁼ si) (Ωᴺ i)) (sym (feed≡ω ε ρc B si (g (br0 ωL (m , pos⁼ si)))))
      (toLwˢ si (ΩJ i
        (Fω ε ρc B si (bs B (fin i) (inl m (pthᶠ si))) (ns B (fin i) (inl m (pthᶠ si))) (g (br0 ωL (m , pos⁼ si))))
        (nzFω ε ρc B si (bs B (fin i) (inl m (pthᶠ si))) (ns B (fin i) (inl m (pthᶠ si))) (g (br0 ωL (m , pos⁼ si))))
        (⊴-trans (wΩ gb m si)
          (cv⊴ (ψs-⊵ ωL ε (ρc , R₀) B (fin i) (inl m (pthᶠ si)) (bs B (fin i) (inl m (pthᶠ si))) (ns B (fin i) (inl m (pthᶠ si)))
                  (g (br0 ωL (m , pos⁼ si))))))))
  chainω {m} {i} si t₀ ε ρc B gb {a} {g = g} e refl h (suc k) =
    subst (Lw m (pos⁼ si) (ψᴺ i (fsT (t₀ ++ a) (γT (t₀ ++ a) (natT i) k))))
      (sym (feed≡ω ε ρc B si (g (vchω ε ρc B (m , pos⁼ si) g (suc k)))))
      (toLwˢ si (subst (λ r → M i (ψᴺ i r)
                   (Fω ε ρc B si (bs B (fin i) (inl m (pthᶠ si))) (ns B (fin i) (inl m (pthᶠ si)))
                       (g (vchω ε ρc B (m , pos⁼ si) g (suc k)))))
        (sym (fsT++ t₀ a (γT (t₀ ++ a) (natT i) k) e))
        (LFω si t₀ ε ρc B gb (bs B (fin i) (inl m (pthᶠ si))) (ns B (fin i) (inl m (pthᶠ si))) (wM gb m si)
          (h (γT (t₀ ++ a) (natT i) k) (vchω ε ρc B (m , pos⁼ si) g (suc k)) (chainω si t₀ ε ρc B gb e refl h k)))))
```
