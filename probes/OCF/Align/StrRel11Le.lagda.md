# 结构关系, 第十一轮: 主线上对层递归的关系族与语义

> 不读记号. 入口 [StrRel11](StrRel11.lagda.md). 在主线折叠 (`HtFeedClosed.At Λ lΛ`) 上, 对一切层 $L$ (含 `hl`, `hΩ`) 定义两世界的结构关系 `Rel L`, 坐标关系由更低层的 `Rel` 给出, **对层递归** (`Rel`/`Below`/`RelS`/`RelAt` 互递归, 对 $L$ 与位置结构递减). 语义 `SemL L` 带两世界, 对齐的运行路径对, 动作对的前提 `HA L` (**上下文按 `Rel L` 相关 ⇒ 输出相关**), 状态与输出按 `Rel` 在一切带对齐的目标对上相关 (`StrRel11Tg.R∀`, `OA`). 本文证明与层无关的六条规则在语义下成立, 对一切层一个证明: `sem-n0`, `sem-n1`, `sem-⨾`, `sem-nl`, `sem-nw`, `sem-pr`. 节点 (`ni`) 与 `nκ` 两条是层相关的部分, 未证 (入口 §3).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (H; LgH)
module OCF.Align.StrRel11Le (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; Vs; D; outS;
  n0; n1; _⨾_; nl; ni; nκ; nw; NZ; AccY)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel11Tg Λ lΛ using (APair; ap-self; ap-tr; TA; R∀; OA; advR)

module P = At Λ lΛ
open P using (Tg; lm; St; Df; yc; d; z; Run; Rpt; Ig; LW; _⊕⟨_⟩_)
```

## 1 关系族: 一层的规则, 坐标关系作参数

`LeF L Lo`: 第 $L$ 层的树之间的结构关系, `Lo` 是节点坐标之间的关系. 规则: `n0`, `n1`, `⨾`, `nl`, 右边前缀 `pr`, **对齐的 `nw`** (`nwA`: 两条前段构成对齐的路径对, 是 `StrRel9Nw.snd-nwA` 的语法版), **节点** (`ni`: 两边的 `StH` 证明可以不同, 坐标层相同, 分支只在**对齐的分支世界对**上比), **`nκ`** (分支同样只在对齐的分支世界对上比). 后两条为什么只取对齐的分支对: `BNi` 与 `Kb` 都在分支路径上做 `cv`, `StrRel11Tg.cvR` 要的正是对齐 (不对齐时见 `StrRel8Neg.¬nwˡ`).

```agda
LoT : H → Set₁
LoT L = ∀ {V V′ k c c′} (r : StH V k L) (r′ : StH V′ k L) → Lg c → Lg c′ → Vs L r c → Vs L r′ c′ → Set

data LeF (L : H) (Lo : LoT L) : ∀ {V V′} → Lg V → Lg V′ → D L V → D L V′ → Set where
  n0ᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L V′} → LeF L Lo lV lV′ n0 x′
  n1ᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} → LeF L Lo lV lV′ n1 n1
  ⨾ᴸ   : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L V′} →
         LeF L Lo lV lV′ x x′ → LeF L Lo lV lV′ y y′ → LeF L Lo lV lV′ (x ⨾ y) (x′ ⨾ y′)
  nlᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {d : ℕ → D L V} {d′ : ℕ → D L V′} →
         (∀ n → LeF L Lo lV lV′ (d n) (d′ n)) → LeF L Lo lV lV′ (nl d) (nl d′)
  prᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L V′} →
         LeF L Lo lV lV′ x x′ → LeF L Lo lV lV′ x (x′ ⨾ y′)
  nwAᴸ : ∀ {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
           {x : D L V₀} {x′ : D L V₀′} →
         APair lV₀ lV₀′ p lV p′ lV′ → LeF L Lo lV₀ lV₀′ x x′ → LeF L Lo lV lV′ (nw p x) (nw p′ x′)
  niᴸ  : ∀ {V V′ k} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {r′ : StH V′ k L}
           {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L r′ W′ → D L W′} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → APair lV lV′ p lc p′ lc′ →
            ∀ y y′ → Lo r r′ lc lc′ y y′ → LeF L Lo lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
         LeF L Lo lV lV′ (ni r u) (ni r′ u′)
  κᴸ   : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {zz zz′ : NZ L}
           {u : ∀ {c} → V ⊲ c → Lg c → D L c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D L c} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → APair lV lV′ p lc p′ lc′ →
            LeF L Lo lc lc′ (u p lc) (u′ p′ lc′)) →
         LeF L Lo lV lV′ (nκ zz u) (nκ zz′ u′)
```

## 2 对层递归

坐标关系沿左边节点的位置往下走到坐标层, 在那里取 `Rel k` (同 `MonoPort6Rel.CtxP`, 但两边世界不同, 两边的 `StH` 证明也可以不同, 所以只沿左边的位置递归, 坐标先用 `outS` 取出). 终止: `Rel L → Below L → RelS L r → RelAt b P → Rel b`, 其中 $b$ 是 $L$ 的结构子项.

```agda
Rel   : ∀ L {V V′} → Lg V → Lg V′ → D L V → D L V′ → Set
Below : ∀ L → LoT L
RelS  : ∀ L {V k c c′} → StH V k L → Lg c → Lg c′ → D k c → D k c′ → Set
RelAt : ∀ b {V k c c′} → k ⊲[ V ] b → Lg c → Lg c′ → D k c → D k c′ → Set

Rel L = LeF L (Below L)
Below L r r′ lc lc′ y y′ = RelS L r lc lc′ (outS r y) (outS r′ y′)
RelS (hs b) (ss P) = RelAt b P
RelS (hl f) (sl n P) = RelAt (f n) P
RelS (hΩ g) (sL e P) = RelAt (g _) P
RelAt b hself = Rel b
RelAt (hs b) (hsuc P) = RelAt b P
RelAt (hl f) (hlim n P) = RelAt (f n) P
RelAt (hΩ g) (hLim e P) = RelAt (g _) P

bot : ∀ t {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D t V′} → Rel t lV lV′ n0 x′
bot t = n0ᴸ

sq : ∀ t {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D t V} {x′ y′ : D t V′} →
     Rel t lV lV′ x x′ → Rel t lV lV′ y y′ → Rel t lV lV′ (x ⨾ y) (x′ ⨾ y′)
sq t = ⨾ᴸ
```

## 3 语义

动作对的前提 `HA L`: 在一切对齐的扩张 $(p, p')$ 上, 上下文按 `Rel L` 相关, 状态按 `R∀ Rel` 相关 ⇒ 输出按 `OA Rel` 相关. `SemL L`: 两边的良基证明与层位置任意, 运行路径构成对齐的路径对, 动作对满足 `HA L`, 上下文与状态相关 ⇒ 输出相关. 上下文在 `HA` 里被读 (`Ai` 把它当坐标), 所以要关系; 这里的关系就是 `Rel L` 本身, 坐标层的关系经 `Below` 由更低层给出.

```agda
HA : ∀ L {W W′} → Lg W → Lg W′ → Ig L W → Ig L W′ → Set
HA L {W} {W′} lW lW′ A₀ A₀′ =
  ∀ {W₁ W₁′} (p : W ⊲ W₁) (p′ : W′ ⊲ W₁′) (lW₁ : Lg W₁) (lW₁′ : Lg W₁′) → APair lW lW′ p lW₁ p′ lW₁′ →
  ∀ w w′ → Rel L lW₁ lW₁′ w w′ → ∀ (Y : St W₁) (Y′ : St W₁′) → R∀ Rel lW₁ lW₁′ Y Y′ →
  OA Rel lW₁ lW₁′ (A₀ p lW₁ w Y) (A₀′ p′ lW₁′ w′ Y′)

SemL : ∀ L {V V′} → Lg V → Lg V′ → D L V → D L V′ → Set
SemL L {V} {V′} lV lV′ x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (ac ac′ : AccY L) (ll : LW L W) (ll′ : LW L W′)
    (q : V ⊲ W) (q′ : V′ ⊲ W′) → APair lV lV′ q lW q′ lW′ →
  ∀ (A₀ : Ig L W) (A₀′ : Ig L W′) → HA L lW lW′ A₀ A₀′ →
  ∀ w w′ → Rel L lW lW′ w w′ → ∀ (Y : St W) (Y′ : St W′) → R∀ Rel lW lW′ Y Y′ →
  OA Rel lW lW′ (Run ac x q lW ll A₀ w Y) (Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′)
```

## 4 与层无关的六条规则 (对一切层一个证明)

每条规则的语义版; 要往上下文里接树的两条 (`⨾`, `nl`) 同时收树的关系 (上下文是语法的).

```agda
sem-n0 : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L V′} → SemL L lV lV′ n0 x′
sem-n0 L lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r {t} T T′ ta = bot t

sem-n1 : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} → SemL L lV lV′ n1 n1
sem-n1 L lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r =
  ha C.self C.self lW lW′ (ap-self lW lW′) w w′ hw Y Y′ r

sem-⨾ : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L V′} →
        Rel L lV lV′ x x′ → SemL L lV lV′ x x′ → SemL L lV lV′ y y′ → SemL L lV lV′ (x ⨾ y) (x′ ⨾ y′)
sem-⨾ L {x = x} {x′ = x′} hx sx sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r {t} T T′ ta =
  sq t (Ox T T′ ta)
       (sy lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha (w ⨾ nw q x) (w′ ⨾ nw q′ x′) (⨾ᴸ hw (nwAᴸ hq hx))
           _ _ (advR Rel sq Y Y′ Δ Δ′ r Ox) T T′ ta)
  where
  Δ = Run ac x q lW ll A₀ w Y
  Δ′ = Run ac′ x′ q′ lW′ ll′ A₀′ w′ Y′
  Ox = sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r

sem-nw : ∀ L {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
           {x : D L V₀} {x′ : D L V₀′} →
         APair lV₀ lV₀′ p lV p′ lV′ → SemL L lV₀ lV₀′ x x′ → SemL L lV lV′ (nw p x) (nw p′ x′)
sem-nw L hp sx lW lW′ ac ac′ ll ll′ q q′ hq = sx lW lW′ ac ac′ ll ll′ (⊲-tr _ q) (⊲-tr _ q′) (ap-tr hp hq)

sem-pr : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L V′} →
         SemL L lV lV′ x x′ → SemL L lV lV′ x (x′ ⨾ y′)
sem-pr L sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
  prᴸ (sx lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta)
```

`nl`: 第 $n$ 段的上下文与状态由 `Rpt` 给出; 对 $n$ 归纳同时维持 "上下文相关, 状态相关".

```agda
module NL (L : H) {V V′} {lV : Lg V} {lV′ : Lg V′} {d : ℕ → D L V} {d′ : ℕ → D L V′}
          (hd : ∀ n → Rel L lV lV′ (d n) (d′ n)) (sd : ∀ n → SemL L lV lV′ (d n) (d′ n))
          {W W′} (lW : Lg W) (lW′ : Lg W′) (ac ac′ : AccY L) (ll : LW L W) (ll′ : LW L W′)
          (q : V ⊲ W) (q′ : V′ ⊲ W′) (hq : APair lV lV′ q lW q′ lW′)
          (A₀ : Ig L W) (A₀′ : Ig L W′) (ha : HA L lW lW′ A₀ A₀′)
          (w : D L W) (w′ : D L W′) (hw : Rel L lW lW′ w w′) (Y : St W) (Y′ : St W′) (r : R∀ Rel lW lW′ Y Y′) where
  Pn : ℕ → D L W × St W
  Pn = Rpt ac d q lW ll A₀ w Y
  Pn′ : ℕ → D L W′ × St W′
  Pn′ = Rpt ac′ d′ q′ lW′ ll′ A₀′ w′ Y′

  St′ : ℕ → Set
  St′ n = Rel L lW lW′ (proj₁ (Pn n)) (proj₁ (Pn′ n)) × R∀ Rel lW lW′ (proj₂ (Pn n)) (proj₂ (Pn′ n))

  out : ∀ n → St′ n → OA Rel lW lW′ (Run ac (d n) q lW ll A₀ (proj₁ (Pn n)) (proj₂ (Pn n)))
                                     (Run ac′ (d′ n) q′ lW′ ll′ A₀′ (proj₁ (Pn′ n)) (proj₂ (Pn′ n)))
  out n (h , s) = sd n lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha _ _ h _ _ s

  go : ∀ n → St′ n
  go zero = hw , r
  go (suc n) = ⨾ᴸ (proj₁ (go n)) (nwAᴸ hq (hd n)) ,
               advR Rel sq (proj₂ (Pn n)) (proj₂ (Pn′ n)) _ _ (proj₂ (go n)) (out n (go n))

sem-nl : ∀ L {V V′} {lV : Lg V} {lV′ : Lg V′} {d : ℕ → D L V} {d′ : ℕ → D L V′} →
         (∀ n → Rel L lV lV′ (d n) (d′ n)) → (∀ n → SemL L lV lV′ (d n) (d′ n)) → SemL L lV lV′ (nl d) (nl d′)
sem-nl L hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r T T′ ta =
  nlᴸ (λ n → N.out n (N.go n) T T′ ta)
  where module N = NL L hd sd lW lW′ ac ac′ ll ll′ q q′ hq A₀ A₀′ ha w w′ hw Y Y′ r
```
