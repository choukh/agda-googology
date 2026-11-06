# 极限高度 (三): 第 ≥1 层的结构关系推广到 ℕ-极限层

> 入口 [MonoPort7](MonoPort7.lagda.md). 不含记号. 由 `probes/Survey/scripts/monoport7/mk_rel.py` 从 [MonoPort6Rel](MonoPort6Rel.lagda.md) 生成 (逐字节可重生成). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 与 `MonoPort6Rel` 只差: 层 `hl f` 上的关系不再是 $\top$, 而是同一个结构关系 `RelM (hl f) (LowT (hl f))` (`RelN`), 上下文同理 (`CxN`); `Fin` 收进 `hl` (`Fin (hl f) = ∀ n → Fin (f n)`, 即不含 Ω-极限), 一切输出律对 `hl` 的那一句照抄 `hs` 的那一句. `RelM` 本来就对任意层定义, 节点 `sl n P` 与 `ss P` 走同一个 `ni⊑`. 新增 `rΩ (hl f)`: $\Omega_{\mathrm{hl}\,f} = 1 ⨾ \mathrm{nl}\,(\lambda n.\ \mathrm{ni}\,(\mathrm{sl}\,n\,\mathrm{hself})\,(\lambda\_ \to 1))$ 与自己相关.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (H; LgH; hz; _⊲[_]_)
module OCF.Align.MonoPort7Rel (Λ : H) (lΛ : LgH Λ) {W : A} (lW : Lg W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtFeedTree using (hs; hl; hΩ; hself; hsuc; hlim; hLim; ss; sl; sL; StH; Vs; Vc; D; outC; inC; outS; inS;
  n0; n1; _⨾_; nl; ni; nκ; nw; Ωd; sum)
open import OCF.Align.StrRelDef lW using (_⊑₀_; z0; o1; sq; lm; wl; wr; pr; tr; u0l; u0r; u1l; u1r; al; al′; ar; ar′; refl₀; preL; val₀)
open import OCF.Align.MonoPort5Rel lW using (module RelM)
import OCF.Align.MonoPort3Gen as Gen

module G = Gen Λ lΛ lW t₀
open G using (module P; o₀; OutLaws; PreLaw) public
```

## 1 不含 Ω-极限的层

```agda
Fin : H → Set
Fin hz = ⊤
Fin (hs b) = Fin b
Fin (hl f) = ∀ n → Fin (f n)
Fin (hΩ g) = ⊥

fin⊲ : ∀ {a b V} → a ⊲[ V ] b → Fin b → Fin a
fin⊲ hself f = f
fin⊲ (hsuc P) f = fin⊲ P f
fin⊲ (hlim n P) f = fin⊲ P (f n)
fin⊲ (hLim e P) ()
```

## 2 关系: 对层与位置递归

```agda
Rel  : ∀ L → D L W → D L W → Set
RelN : ∀ L → D L W → D L W → Set
CxN  : ∀ L → D L W → D L W → Set
LowT : ∀ L {k} (r : StH W k L) → Vs L r W → Vs L r W → Set
CtxP : ∀ b {k} (P : k ⊲[ W ] b) → Vc b P W → Vc b P W → Set
Ctx  : ∀ k → D k W → D k W → Set

RelN L = RelM._⊑_ L (LowT L)
CxN L x x′ = RelN L x x′ × (RelM.Ok L (LowT L) x × RelM.Ok L (LowT L) x′)

Rel hz x x′ = x ⊑₀ x′
Rel (hs b) = RelN (hs b)
Rel (hl f) = RelN (hl f)
Rel (hΩ g) _ _ = ⊤

LowT hz ()
LowT (hs b) (ss P) = CtxP b P
LowT (hl f) (sl n P) = CtxP (f n) P
LowT (hΩ g) (sL e P) = CtxP (g _) P

CtxP b hself = Ctx b
CtxP (hs b) (hsuc P) = CtxP b P
CtxP (hl f) (hlim n P) = CtxP (f n) P
CtxP (hΩ g) (hLim e P) = CtxP (g _) P

-- 第 ≥1 层的上下文: 相关, 且沿 ⨾ 左脊两边自比 (同 MonoPort5One 的 Cx₁)
Ctx hz x x′ = x ⊑₀ x′
Ctx (hs b) = CxN (hs b)
Ctx (hl f) = CxN (hl f)
Ctx (hΩ g) _ _ = ⊤

module RL (L : H) = RelM L (LowT L)
module R (b : H) = RL (hs b)

Rf : ∀ t → D t W → Set
Rf t x = Rel t x x
```

坐标关系沿位置的搬运 (障碍 (iii)): 对 $P$ 归纳, 每一步定义性.

```agda
lowOutC : ∀ b {k} (P : k ⊲[ W ] b) {z z′ : Vc b P W} → CtxP b P z z′ → Ctx k (outC P z) (outC P z′)
lowOutC b hself h = h
lowOutC (hs b) (hsuc P) h = lowOutC b P h
lowOutC (hl f) (hlim n P) h = lowOutC (f n) P h
lowOutC (hΩ g) (hLim e P) h = lowOutC (g _) P h

lowInC : ∀ b {k} (P : k ⊲[ W ] b) {z z′ : D k W} → Ctx k z z′ → CtxP b P (inC P z) (inC P z′)
lowInC b hself h = h
lowInC (hs b) (hsuc P) h = lowInC b P h
lowInC (hl f) (hlim n P) h = lowInC (f n) P h
lowInC (hΩ g) (hLim e P) h = lowInC (g _) P h

lowOut : ∀ L {k} (r : StH W k L) {z z′ : Vs L r W} → LowT L r z z′ → Ctx k (outS r z) (outS r z′)
lowOut (hs b) (ss P) h = lowOutC b P h
lowOut (hl f) (sl n P) h = lowOutC (f n) P h
lowOut (hΩ g) (sL e P) h = lowOutC (g _) P h

lowIn : ∀ L {k} (r : StH W k L) {z z′ : D k W} → Ctx k z z′ → LowT L r (inS r z) (inS r z′)
lowIn (hs b) (ss P) h = lowInC b P h
lowIn (hl f) (sl n P) h = lowInC (f n) P h
lowIn (hΩ g) (sL e P) h = lowInC (g _) P h

-- 上下文关系的两边自比与关系本身
cxRel : ∀ k {z z′} → Ctx k z z′ → Rel k z z′
cxRel hz h = h
cxRel (hs b) h = proj₁ h
cxRel (hl f) h = proj₁ h
cxRel (hΩ g) h = tt

cxL : ∀ k {z z′} → Ctx k z z′ → Ctx k z z
cxL hz {z} h = refl₀ z
cxL (hs b) (_ , (o , _)) = RL.OkRf (hs b) o , (o , o)
cxL (hl f) (_ , (o , _)) = RL.OkRf (hl f) o , (o , o)
cxL (hΩ g) h = tt

cxR : ∀ k {z z′} → Ctx k z z′ → Ctx k z′ z′
cxR hz {z′ = z′} h = refl₀ z′
cxR (hs b) (_ , (_ , o′)) = RL.OkRf (hs b) o′ , (o′ , o′)
cxR (hl f) (_ , (_ , o′)) = RL.OkRf (hl f) o′ , (o′ , o′)
cxR (hΩ g) h = tt
```

## 3 输出律: 对目标层分情形

```agda
r0 : ∀ t {x} → Rel t n0 x
r0 hz = z0
r0 (hs b) = RelM.n0⊑
r0 (hl f) = RelM.n0⊑
r0 (hΩ g) = tt

r1 : ∀ t → Rel t n1 n1
r1 hz = o1
r1 (hs b) = RelM.n1⊑
r1 (hl f) = RelM.n1⊑
r1 (hΩ g) = tt

r⨾ : ∀ t {x y x′ y′} → Rf t x → Rf t x′ → Rel t x x′ → Rel t y y′ → Rel t (x ⨾ y) (x′ ⨾ y′)
r⨾ hz a a′ h k = sq h k
r⨾ (hs b) a a′ h k = RelM.⨾⊑ a a′ h k
r⨾ (hl f) a a′ h k = RelM.⨾⊑ a a′ h k
r⨾ (hΩ g) a a′ h k = tt

rnl : ∀ t {d d′ : ℕ → D t W} → (∀ n → Rf t (d n)) → (∀ n → Rf t (d′ n)) → (∀ n → Rel t (d n) (d′ n)) → Rel t (nl d) (nl d′)
rnl hz r r′ h = lm h
rnl (hs b) r r′ h = RelM.nl⊑ r r′ h
rnl (hl f) r r′ h = RelM.nl⊑ r r′ h
rnl (hΩ g) r r′ h = tt

rtr : ∀ t {x y z} → Rel t x y → Rel t y z → Rel t x z
rtr hz h k = tr h k
rtr (hs b) h k = RelM.tr h k
rtr (hl f) h k = RelM.tr h k
rtr (hΩ g) h k = tt

u0L : ∀ t {x x′} → Rel t x x′ → Rel t (n0 ⨾ x) x′
u0L hz h = u0l h
u0L (hs b) h = RelM.u0ˡ h
u0L (hl f) h = RelM.u0ˡ h
u0L (hΩ g) h = tt

u0R : ∀ t {x x′} → Rel t x x′ → Rel t x (n0 ⨾ x′)
u0R hz h = u0r h
u0R (hs b) h = RelM.u0ʳ h
u0R (hl f) h = RelM.u0ʳ h
u0R (hΩ g) h = tt

u1L : ∀ t {x x′} → Rel t x x′ → Rel t (x ⨾ n0) x′
u1L hz h = u1l h
u1L (hs b) h = RelM.u1ˡ h
u1L (hl f) h = RelM.u1ˡ h
u1L (hΩ g) h = tt

u1R : ∀ t {x x′} → Rel t x x′ → Rel t x (x′ ⨾ n0)
u1R hz h = u1r h
u1R (hs b) h = RelM.u1ʳ h
u1R (hl f) h = RelM.u1ʳ h
u1R (hΩ g) h = tt

asL : ∀ t {x y z s} → Rf t x → Rf t y → Rf t z → Rel t (x ⨾ (y ⨾ z)) s → Rel t ((x ⨾ y) ⨾ z) s
asL hz a b c h = al h
asL (hs _) a b c h = RelM.asˡ a b c h
asL (hl f) a b c h = RelM.asˡ a b c h
asL (hΩ g) a b c h = tt

asL′ : ∀ t {x y z s} → Rf t x → Rf t y → Rf t z → Rel t ((x ⨾ y) ⨾ z) s → Rel t (x ⨾ (y ⨾ z)) s
asL′ hz a b c h = al′ h
asL′ (hs _) a b c h = RelM.asˡ′ a b c h
asL′ (hl f) a b c h = RelM.asˡ′ a b c h
asL′ (hΩ g) a b c h = tt

asR : ∀ t {x y z s} → Rf t x → Rf t y → Rf t z → Rel t s ((x ⨾ y) ⨾ z) → Rel t s (x ⨾ (y ⨾ z))
asR hz a b c h = ar h
asR (hs _) a b c h = RelM.asʳ a b c h
asR (hl f) a b c h = RelM.asʳ a b c h
asR (hΩ g) a b c h = tt

asR′ : ∀ t {x y z s} → Rf t x → Rf t y → Rf t z → Rel t s (x ⨾ (y ⨾ z)) → Rel t s ((x ⨾ y) ⨾ z)
asR′ hz a b c h = ar′ h
asR′ (hs _) a b c h = RelM.asʳ′ a b c h
asR′ (hl f) a b c h = RelM.asʳ′ a b c h
asR′ (hΩ g) a b c h = tt

rpre : ∀ t {x x′} {d d′ : ℕ → D t W} → Rf t x → Rf t x′ → (∀ n → Rf t (d n)) → (∀ n → Rf t (d′ n)) →
       Rel t x x′ → (∀ n → Rel t (d n) (d′ n)) → ∀ k → Rel t (x ⨾ preL d k) (x′ ⨾ nl d′)
rpre hz a a′ r r′ h hd k = pr h hd k
rpre (hs b) a a′ r r′ h hd k = RelM.pre⊑ a a′ r r′ h hd k
rpre (hl f) a a′ r r′ h hd k = RelM.pre⊑ a a′ r r′ h hd k
rpre (hΩ g) a a′ r r′ h hd k = tt

rnwl : ∀ t {x x′} → Rel t x x′ → Rel t (nw C.self x) x′
rnwl hz h = wl h
rnwl (hs b) h = RelM.nwˡ h
rnwl (hl f) h = RelM.nwˡ h
rnwl (hΩ g) h = tt

rnwr : ∀ t {x x′} → Rel t x x′ → Rel t x (nw C.self x′)
rnwr hz h = wr h
rnwr (hs b) h = RelM.nwʳ h
rnwr (hl f) h = RelM.nwʳ h
rnwr (hΩ g) h = tt

-- 节点: 第 0 层没有节点
rni : ∀ t {k} (r : StH W k t) {u u′ : ∀ {W′} → W ⊲ W′ → Lg W′ → Vs t r W′ → D t W′} →
      (∀ z z′ → LowT t r z z′ → Rel t (u C.self lW z) (u C.self lW z′)) →
      (∀ z z′ → LowT t r z z′ → Rel t (u′ C.self lW z) (u′ C.self lW z′)) →
      (∀ z z′ → LowT t r z z′ → Rel t (u C.self lW z) (u′ C.self lW z′)) → Rel t (ni r u) (ni r u′)
rni (hs b) r mu mu′ cr = RelM.ni⊑ r mu mu′ cr
rni (hl f) r mu mu′ cr = RelM.ni⊑ r mu mu′ cr
rni (hΩ g) r mu mu′ cr = tt

rΩ : ∀ t → Rf t (Ωd t {W})
rΩ hz = o1
rΩ (hs b) = RelM.⨾⊑ RelM.n1⊑ RelM.n1⊑ RelM.n1⊑ (RelM.ni⊑ (ss hself) (λ _ _ _ → RelM.n1⊑) (λ _ _ _ → RelM.n1⊑) (λ _ _ _ → RelM.n1⊑))
rΩ (hl f) = RelM.⨾⊑ RelM.n1⊑ RelM.n1⊑ RelM.n1⊑ (RelM.nl⊑ (λ n → ni₁ n) (λ n → ni₁ n) (λ n → ni₁ n))
  where
  ni₁ : ∀ n → RelN (hl f) (ni (sl n hself) (λ _ _ _ → n1)) (ni (sl n hself) (λ _ _ _ → n1))
  ni₁ n = RelM.ni⊑ (sl n hself) (λ _ _ _ → RelM.n1⊑) (λ _ _ _ → RelM.n1⊑) (λ _ _ _ → RelM.n1⊑)
rΩ (hΩ g) = tt

rnwT : ∀ t {x} → Rf t x → Rf t (nw C.self x)
rnwT t r = rnwl t (rnwr t r)
```

## 4 观测: 一切目标, 一切位置

```agda
Tt : ∀ {t} → t ⊲[ W ] Λ → P.Tg W t W
Tt tm = P.tg C.self tm lW

infix 4 _≼_
_≼_ : P.Df W → P.Df W → Set
Δ ≼ Δ′ = ∀ {t} (tm : t ⊲[ W ] Λ) → Rel t (P.yc Δ (Tt tm)) (P.yc Δ′ (Tt tm))

⨾≼ : ∀ {a b a′ b′} → a ≼ a → a′ ≼ a′ → a ≼ a′ → b ≼ b′ → (a P.⨾ᴰ b) ≼ (a′ P.⨾ᴰ b′)
⨾≼ ra ra′ h k {t} tm = r⨾ t (ra tm) (ra′ tm) (h tm) (k tm)

nl≼ : ∀ {F F′ : ℕ → P.Df W} → (∀ n → F n ≼ F n) → (∀ n → F′ n ≼ F′ n) → (∀ n → F n ≼ F′ n) → P.nlᴰ F ≼ P.nlᴰ F′
nl≼ r r′ h {t} tm = rnl t (λ n → r n tm) (λ n → r′ n tm) (λ n → h n tm)

tr≼ : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
tr≼ h k {t} tm = rtr t (h tm) (k tm)

u0≼ˡ : ∀ {a a′} → a ≼ a′ → (P.zeroD P.⨾ᴰ a) ≼ a′
u0≼ˡ h {t} tm = u0L t (h tm)
u0≼ʳ : ∀ {a a′} → a ≼ a′ → a ≼ (P.zeroD P.⨾ᴰ a′)
u0≼ʳ h {t} tm = u0R t (h tm)
u1≼ˡ : ∀ {a a′} → a ≼ a′ → (a P.⨾ᴰ P.zeroD) ≼ a′
u1≼ˡ h {t} tm = u1L t (h tm)
u1≼ʳ : ∀ {a a′} → a ≼ a′ → a ≼ (a′ P.⨾ᴰ P.zeroD)
u1≼ʳ h {t} tm = u1R t (h tm)

as≼ˡ : ∀ {a b c s} → a ≼ a → b ≼ b → c ≼ c → (a P.⨾ᴰ (b P.⨾ᴰ c)) ≼ s → ((a P.⨾ᴰ b) P.⨾ᴰ c) ≼ s
as≼ˡ ra rb rc h {t} tm = asL t (ra tm) (rb tm) (rc tm) (h tm)
as≼ˡ′ : ∀ {a b c s} → a ≼ a → b ≼ b → c ≼ c → ((a P.⨾ᴰ b) P.⨾ᴰ c) ≼ s → (a P.⨾ᴰ (b P.⨾ᴰ c)) ≼ s
as≼ˡ′ ra rb rc h {t} tm = asL′ t (ra tm) (rb tm) (rc tm) (h tm)
as≼ʳ : ∀ {a b c s} → a ≼ a → b ≼ b → c ≼ c → s ≼ ((a P.⨾ᴰ b) P.⨾ᴰ c) → s ≼ (a P.⨾ᴰ (b P.⨾ᴰ c))
as≼ʳ ra rb rc h {t} tm = asR t (ra tm) (rb tm) (rc tm) (h tm)
as≼ʳ′ : ∀ {a b c s} → a ≼ a → b ≼ b → c ≼ c → s ≼ (a P.⨾ᴰ (b P.⨾ᴰ c)) → s ≼ ((a P.⨾ᴰ b) P.⨾ᴰ c)
as≼ʳ′ ra rb rc h {t} tm = asR′ t (ra tm) (rb tm) (rc tm) (h tm)

O : OutLaws
O = record { _≼_ = _≼_ ; L0 = λ {Δ} {t} tm → r0 t ; L⨾ = ⨾≼ ; Lnl = nl≼ ; Ltr = tr≼ ; Lu0ˡ = u0≼ˡ ; Lu0ʳ = u0≼ʳ ; Lu1ˡ = u1≼ˡ ; Lu1ʳ = u1≼ʳ
           ; Lasˡ = as≼ˡ ; Lasˡ′ = as≼ˡ′ ; Lasʳ = as≼ʳ ; Lasʳ′ = as≼ʳ′ }

opre : (F : ℕ → P.Df W) {t : H} (T : P.Tg W t W) (k : ℕ) → P.yc (G.preᴰ F k) T ≡ preL (λ n → P.yc (F n) T) k
opre F T zero = refl
opre F T (suc k) = cong (λ s → s ⨾ P.yc (F k) T) (opre F T k)

preO : PreLaw O
preO {a} {a′} {F} {F′} ra ra′ rF rF′ h hF k {t} tm =
  subst (λ s → Rel t (P.yc a (Tt tm) ⨾ s) (P.yc a′ (Tt tm) ⨾ nl (λ n → P.yc (F′ n) (Tt tm)))) (sym (opre F (Tt tm) k))
    (rpre t (ra tm) (ra′ tm) (λ n → rF n tm) (λ n → rF′ n tm) (h tm) (λ n → hF n tm) k)

proj₀ : ∀ {Δ Δ′} → Δ ≼ Δ′ → o₀ Δ ⊑₀ o₀ Δ′
proj₀ h = h t₀
```

## 5 与实例无关的动作前提

核 `Core` 的 `HA` 用核内的记录 `Cx`, 两个参数不同的核实例给出两个不同的记录类型 (上一组的障碍 (ii)). 这里写一个不依赖实例的版本 `HAK`, 只用 `Ctx`; 到每个核实例的换算是一行 (`MonoPort7Lay`).

```agda
Good : P.St W → Set
Good Y = P.d Y ≼ P.d Y

SRel : P.St W → P.St W → Set
SRel Y Y′ = (G.vY Y ≤ G.vY Y′) × (P.d Y ≼ P.d Y′)

Obs : A → A → P.Df W → P.Df W → Set
Obs c c′ Δ Δ′ = (sum c (o₀ Δ) ≤ sum c′ (o₀ Δ′)) × (Δ ≼ Δ′)

HAK : ∀ k → P.Ig k W → P.Ig k W → Set
HAK k A₀ A₁ = ∀ w w′ c c′ Y Y′ → Ctx k w w′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (A₀ C.self lW w Y) (A₁ C.self lW w′ Y′)

-- 观测由 ≼ 给出: 第 0 层的读数单调
obs : ∀ {c c′ Δ Δ′} → c ≤ c′ → Δ ≼ Δ′ → Obs c c′ Δ Δ′
obs cb h = val₀ (h t₀) cb , h
```
