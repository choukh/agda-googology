# Fab6 (三): 层的代数 — 每层带自己的折叠, 下一层由 `ext` / `supL` / `diag` 写出

> 不含记号. 入口 [Fab6](Fab6.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只导入 `Fab6Base`, `Fab6Fold`, `Fab6` (取 `leg`, `FGH`).
>
> **这一篇做什么.** 入口文件的 `ΦX` 只处理一个外部种类 ($\Omega_\Omega$), 对应 CRw 的 $X_1$ 站. 这里把 "一层" 写成记录 `FL`: 外部种类 `X`, 这一层的地板 `fl`, 和**这一层自己的折叠** `Ψ` (把这一层的树折到底层 `S₁` 上的塔的任一层 $t$). 然后三个算子:
>
> - `ext L`: 在 $L$ 上加一个外部种类, 坐标 $y$ 处的分支是 **$L$ 上高度 $y$ 的塔的树** (读 $\Omega_{\alpha+\Omega}$, 若 $L$ 读 $\Omega_\alpha$); 它的折叠调用 $L$ 的折叠与同底折叠 `Φ`.
> - `supL F`: ℕ 个层的并 (外部种类取和), 地板取部分和.
> - `diag F`: 对 Cd-族 $F$ 的对角: 一个外部种类, 坐标 $c$ 处的分支是第 $F\,c$ 层的树 (读 $\sup_{c<\Omega_1}$).
>
> 闭项对一切层一条定义 (`clL`): 先用这一层的折叠折到 $\Omega_1$ 层, 再用同底折叠把 $\Omega_1$ 折到第 0 层. 证书由形状给出 (`Sh-Φ`), 不读 `Ψ`. 于是 "下一站的定义" 不再是判断: 是 `ext`, 或 `diag` 作用在已有的族上; 闭包定理 (`Lg-clL`) 对一切层一条, 不按站写.
>
> **底层换成 `S₁`.** `S₁ = step X⊥ S⊥` 是只有一个普通种类 $\Omega_1$ (坐标是可数树) 的结构. 每层的折叠 `Ψ` **不坍缩** $\Omega_1$: $\Omega_1$ 是底种类, 一律留; 外部结点 (共尾度都是 $\Omega_1$) 留成 $\Omega_1$-结点, 分支由下一层的折叠给出. 唯一的坍缩 (带回灌的链) 在最后一步 `Φ (hs hz) → hz` 里 (同底折叠在第 0 层的 `same` 子句). 所以 `Ψ` 不需要 "决定": 入口文件 `nodeX` 里比较 $1$ 与 $t$ 的那一步, 在这里是 "$\Omega_1$ 是底种类" 这句话.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.Fab6Lay where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.Fab6Base
open import OCF.Lean.Fab6Fold
open import OCF.Lean.Fab6 using (leg; Lg-leg; FGH)
```

## §1 底层 `S₁`, 嵌入

```agda
S₁ : KS
S₁ = step X⊥ S⊥

Ω₁ : K S₁
Ω₁ = inj₂ tt

-- 把 S 上的树嵌入 S 上第 t 层的塔 (底种类沿 emb)
module _ {X : XK} {S : KS} where
  embT : ∀ t → HB X S → HB X (Tw X S t)
  embT t hz = hz
  embT t (hs h) = hs (embT t h)
  embT t (hl f) = hl (λ n → embT t (f n))
  embT t (hΩ κ g) = hΩ (emb t κ) (λ c → embT t (g (frE t κ c)))
  embT t (hE x p g) = hE x (embT t p) g
```

## §2 层

```agda
record FL : Set₁ where
  field
    X  : XK
    fl : HB X S₁
    Ψ  : ∀ t → HB X S₁ → HB X⊥ (Tw X⊥ S₁ t)
open FL public
```

折叠的公共部分: $0$, 后继, ℕ-极限逐点; $\Omega_1$ 留 (底种类); 外部结点交给处理子 `hE?` (收到折好的前缀).

```agda
module Gen (X : XK)
  (hE? : ∀ t → (x : KX X) → HB X⊥ (Tw X⊥ S₁ t) → ((y : EX X x) → Br X x y) → HB X⊥ (Tw X⊥ S₁ t)) where
  Ψg : ∀ t → HB X S₁ → HB X⊥ (Tw X⊥ S₁ t)
  Ψg t hz = hz
  Ψg t (hs h) = hs (Ψg t h)
  Ψg t (hl f) = hl (λ n → Ψg t (f n))
  Ψg t (hΩ (inj₁ ()) _)
  Ψg t (hΩ (inj₂ _) g) = hΩ (emb t Ω₁) (λ c → Ψg t (g (frE t Ω₁ c)))
  Ψg t (hE x p g) = hE? t x (Ψg t p) g
```

**第 0 层**: 没有外部种类, 地板是 $\Omega_1$ (分支 $c\mapsto c$).

```agda
L₀ : FL
L₀ = record { X = X⊥ ; fl = hΩ Ω₁ up ; Ψ = Gen.Ψg X⊥ (λ t x → ⊥-elim x) }
```

## §3 `ext`: 下一个 $\Omega_1$-共尾的种类

新种类的坐标是可数树 $y$, 分支是 $L$ 上高度 $y$ 的塔的树. 地板: 分支取塔的地板 (底是 $L$ 的地板). 折叠: 旧外部种类交回 $L$ 的折叠; 新种类留成 $\Omega_1$-结点, 坐标 $c$ 处的分支 = 先用同底折叠把高度 $\mathrm{leg}\,c$ 的塔折到 $L$ 层 (种子 $L$ 的地板), 再用 $L$ 的折叠折到 $t$.

```agda
extX : FL → XK
extX L = record
  { KX = KX (X L) ⊎ ⊤
  ; EX = λ { (inj₁ x) → EX (X L) x ; (inj₂ _) → Cd }
  ; Br = λ { (inj₁ x) → Br (X L) x ; (inj₂ _) y → HB (X L) (Tw (X L) S₁ y) }
  ; LgBr = λ { (inj₁ x) → LgBr (X L) x ; (inj₂ _) y → LgB } }

ext : FL → FL
ext L = record
  { X = extX L
  ; fl = hE (inj₂ tt) hz (topT (X L) S₁ (fl L))
  ; Ψ = Gen.Ψg (extX L) h }
  where
  h : ∀ t (x : KX (extX L)) → HB X⊥ (Tw X⊥ S₁ t) → ((y : EX (extX L) x) → Br (extX L) x y) → HB X⊥ (Tw X⊥ S₁ t)
  h t (inj₁ x) bp g = bp ⊞ Ψ L t (hE x hz g)
  h t (inj₂ _) bp g = bp ⊞ hΩ (emb t Ω₁) (λ c → Ψ L t (br (frE t Ω₁ c)))
    where
    br : Cd → HB (X L) S₁
    br c′ = Φ (leg c′) (wf _) (Lg-leg c′) hz (z⊲ᴮ _) (fl L) (g (leg c′))
```

## §4 `supL`: ℕ 个层的并

```agda
supX : (ℕ → FL) → XK
supX F = record
  { KX = Σ ℕ (λ n → KX (X (F n))) ; EX = λ x → EX (X (F (proj₁ x))) (proj₂ x)
  ; Br = λ x → Br (X (F (proj₁ x))) (proj₂ x) ; LgBr = λ x → LgBr (X (F (proj₁ x))) (proj₂ x) }

module _ (F : ℕ → FL) where
  ιX : ∀ n → HB (X (F n)) S₁ → HB (supX F) S₁
  ιX n hz = hz
  ιX n (hs h) = hs (ιX n h)
  ιX n (hl f) = hl (λ m → ιX n (f m))
  ιX n (hΩ κ g) = hΩ κ (λ c → ιX n (g c))
  ιX n (hE x p g) = hE (n , x) (ιX n p) g

supL : (ℕ → FL) → FL
supL F = record
  { X = supX F
  ; fl = hl (Σ⁺ (λ n → ιX F n (fl (F n))))
  ; Ψ = Gen.Ψg (supX F) (λ t x bp g → bp ⊞ Ψ (F (proj₁ x)) t (hE (proj₂ x) hz g)) }
```

## §5 `diag`: 对 Cd-族取对角

一个外部种类, 坐标 $c$ 处的分支是第 $F\,c$ 层的树. 地板: 分支取各层的地板. 折叠: 留成 $\Omega_1$-结点, 分支交给第 $c$ 层的折叠.

```agda
diagX : (Cd → FL) → XK
diagX F = record { KX = ⊤ ; EX = λ _ → Cd ; Br = λ _ c → HB (X (F c)) S₁ ; LgBr = λ _ c → LgB }

diag : (Cd → FL) → FL
diag F = record
  { X = diagX F
  ; fl = hE tt hz (λ c → fl (F c))
  ; Ψ = Gen.Ψg (diagX F) (λ t _ bp g → bp ⊞ hΩ (emb t Ω₁) (λ c → Ψ (F (frE t Ω₁ c)) t (g (frE t Ω₁ c)))) }
```

## §6 闭项对一切层一条定义

先用这一层的折叠折到 $\Omega_1$ 层 ($t=0$, 即 `S₁`), 再用同底折叠 (`Tw X⊥ S⊥ 1 = S₁`) 把 $\Omega_1$ 折到第 0 层: $\Omega_1$ 在那里是第 0 层的新种类, 目标 $0$, 取带回灌的链.

```agda
clL : FL → Cd
clL L = Φ (hs hz) (wf _) tt hz (hsuc hself) hz (Ψ L hz (fl L))

Lg-clL : ∀ L → LgB (clL L)
Lg-clL L = sh→lg _ (Sh-Φ (hs hz) (wf _) tt hz (hsuc hself) hz (Ψ L hz (fl L)))

fgh : FL → ℕ → ℕ
fgh L = FGH (clL L)
```

## §7 沿 Cd 迭代一个算子, 与一个塔的塔

`It G L c`: 把算子 $G$ 从 $L$ 起沿 $c$ 迭代, 极限处取 `supL`. `pow = It ext` (读 $\Omega_{\alpha+\Omega\cdot c}$); `P k`: 第 $k+1$ 个算子 = 沿 Cd 迭代 "对上一个算子取对角" (读 $\Omega_{\alpha+\Omega^{k+1}\cdot c}$); `Pc`: 同样的事对 Cd 做, 极限处取 `supL`.

```agda
It : (FL → FL) → FL → Cd → FL
It G L hz = L
It G L (hs c) = G (It G L c)
It G L (hl f) = supL (λ n → It G L (f n))
It G L (hΩ () _)
It G L (hE () _ _)

pow : FL → Cd → FL
pow = It ext

P : ℕ → FL → Cd → FL
P zero = pow
P (suc k) = It (λ L → diag (P k L))

Pc : Cd → FL → Cd → FL
Pc hz = pow
Pc (hs c) = It (λ L → diag (Pc c L))
Pc (hl f) L c = supL (λ n → Pc (f n) L c)
Pc (hΩ () _)
Pc (hE () _ _)
```

## §8 闭项

```agda
one : Cd
one = hs hz

T₀ TΩΩ TΩΩ₂ TΩ² TΩ³ TΩ^ω TΩ^Ω : Cd
T₀ = clL L₀                                   -- Ω₁ 折到 0
TΩΩ = clL (ext L₀)                            -- Ω_Ω
TΩΩ₂ = clL (pow L₀ (hs one))                  -- Ω_{Ω·2}
TΩ² = clL (diag (pow L₀))                     -- Ω_{Ω²}
TΩ³ = clL (diag (P 1 L₀))                     -- Ω_{Ω³}
TΩ^ω = clL (supL (λ k → P k L₀ one))          -- Ω_{Ω^ω}
TΩ^Ω = clL (diag (λ c → Pc c L₀ one))         -- Ω_{Ω^Ω}

Lg-TΩ^Ω : LgB TΩ^Ω
Lg-TΩ^Ω = Lg-clL (diag (λ c → Pc c L₀ one))

fghΩ^Ω : ℕ → ℕ
fghΩ^Ω = fgh (diag (λ c → Pc c L₀ one))
```

(右边注释是读法, 全是判断, 见入口 §5.)
