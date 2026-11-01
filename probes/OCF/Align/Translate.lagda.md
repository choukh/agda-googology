# EBO 对齐: 镜像表记到 EBO 的翻译定理

> 树侧的对齐 ([Finite](Finite.lagda.md), [Omega1](Omega1.lagda.md)) 不直接比较树与 [EBO](EBO.lagda.md), 而是经过一个**镜像表记**: 主项 `ψ u a` 的下标是自然数 `u : ℕ`, 其余规则逐条抄自 EBO, 只把 `cmpᵀ (sucT μ) u` 换成 `cmp (suc μ) u`. Omega1 证明树的基本列与镜像表记一致; 镜像表记与 EBO 的一致此前只在 12 个样例上用 `refl` 核对 (Omega1 §7.3).
>
> 本文把它升级为定理. 翻译 `toE` 把下标 $u$ 换成 `natT u`. 对**全部**镜像项 (下标是任意自然数, 不限于 $\le1$), `toE` 与 `cof`, `pred`, ω-基本列, Ω-基本列, γ-链逐字交换, **无前提**; 带证书的 `fsn↓`, `fsT↓`, `γ↓` 的值经 [EBO](EBO.lagda.md) §6 的引理随之对齐. 推论: `toE` 是单射, 其像恰是"下标全为 `natT k`"的 EBO 项, 这个子集对 `pred`, `fsn↓`, `fsT↓`, `γ↓` 封闭.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Translate where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Properties using (∷-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

import OCF.Align.EBO as E
open import OCF.Align.Omega1 using
  ( T; P; ψ; natT; Cmp; lt; eq; gt; cmp; Cof; c0; c1; cω; cΩ
  ; cofψ₊; cofA; cof; cofP; pred; fsΩ; fsΩ₊; fsΩc; γ; rep; fs; fsn; fsn₊; fsnc
  ; toE; toEP )
```

镜像表记的名字 (`T`, `ψ`, `cof`, `fs`, ...) 直接打开; EBO 的名字一律带前缀 `E.`. 翻译本身沿用 Omega1 §7.3 的定义:

    toE  : T → E.T                    toE []       = []
    toEP : P → E.PT                   toE (x ∷ xs) = toEP x ∷ toE xs
                                      toEP (ψ u a) = E.ψ (E.natT u) (toE a)

## §1 共尾度与比较的翻译

两边各有自己的 `Cmp` 与 `Cof`. 共尾度的翻译把 $\Omega_{\mu+1}$ 的下标 $\mu$ 也换成 `natT μ`.

```agda
trCmp : Cmp → E.Cmp
trCmp lt = E.lt
trCmp eq = E.eq
trCmp gt = E.gt

trCof : Cof → E.Cof
trCof c0     = E.c0
trCof c1     = E.c1
trCof cω     = E.cω
trCof (cΩ μ) = E.cΩ (E.natT μ)
```

自然数的项: 镜像的 `natT n` 翻译成 EBO 的 `natT n` (两边都是 $n$ 个 $\mathbf 1$), $n+1$ 在 EBO 里就是 `sucT (natT n)`. 比较两个 `natT` 时, `cmpᵀ` 逐项比较 $\mathbf 1$ 与 $\mathbf 1$, `with` 的辅助函数在具体的 $\mathbf 1$ 上归约为 `eq`, 于是 `cmpᵀ (natT m) (natT n)` 就是自然数的比较. 合起来得到规则 5/6 分界的翻译 `cmp-toE`: EBO 的 `cmpᵀ (sucT (natT ν)) (natT u)` 等于镜像的 `cmp (suc ν) u`.

```agda
toE-natT : ∀ n → toE (natT n) ≡ E.natT n
toE-natT zero    = refl
toE-natT (suc n) = cong (E.𝟏 ∷_) (toE-natT n)

sucT-natT : ∀ n → E.sucT (E.natT n) ≡ E.natT (suc n)
sucT-natT zero    = refl
sucT-natT (suc n) = cong (E.𝟏 ∷_) (sucT-natT n)

cmpT-natT : ∀ m n → E.cmpᵀ (E.natT m) (E.natT n) ≡ trCmp (cmp m n)
cmpT-natT zero    zero    = refl
cmpT-natT zero    (suc n) = refl
cmpT-natT (suc m) zero    = refl
cmpT-natT (suc m) (suc n) = cmpT-natT m n

cmp-toE : ∀ ν u → E.cmpᵀ (E.sucT (E.natT ν)) (E.natT u) ≡ trCmp (cmp (suc ν) u)
cmp-toE ν u = trans (cong (λ s → E.cmpᵀ s (E.natT u)) (sucT-natT ν)) (cmpT-natT (suc ν) u)
```

## §2 共尾度

**定理 `cof-toE`.** 对每个镜像项 $t$, `E.cof (toE t) ≡ trCof (cof t)`.

逐条对应: 和取末项, 两边相同; $\psi_0(0)=\mathbf 1$ 两边都是 `c1`; $\psi_{\mu+1}(0)$ 在镜像里直接是 `cΩ μ`, 在 EBO 里走 `cofψ0` 的后继分支得 `cΩ (pred (natT (suc μ)))`, 用 `cof-natT`, `pred-natT` (EBO §6) 换成 `cΩ (natT μ)`; $\psi_u(b)$ 两边都是 `cofA u (cof b)`, 规则 5/6 的分派由 `cmp-toE` 对齐. 镜像里没有 EBO `cofψ0` 的 `cω`/`cΩ` 分支 (自然数下标不是极限), 翻译也碰不到它们.

```agda
cofψ₊-toE : ∀ u μ m → E.cofψ₊ (E.natT u) (E.natT μ) (trCmp m) ≡ trCof (cofψ₊ u μ m)
cofψ₊-toE u μ lt = refl
cofψ₊-toE u μ eq = refl
cofψ₊-toE u μ gt = refl

cofA-toE : ∀ u c → E.cofA (E.natT u) (trCof c) ≡ trCof (cofA u c)
cofA-toE u c0     = refl
cofA-toE u c1     = refl
cofA-toE u cω     = refl
cofA-toE u (cΩ μ) =
  trans (cong (E.cofψ₊ (E.natT u) (E.natT μ)) (cmp-toE μ u)) (cofψ₊-toE u μ (cmp (suc μ) u))

cof-toE  : ∀ t → E.cof (toE t) ≡ trCof (cof t)
cofP-toE : ∀ x → E.cofP (toEP x) ≡ trCof (cofP x)
cof-toE []           = refl
cof-toE (x ∷ [])     = cofP-toE x
cof-toE (x ∷ y ∷ ys) = cof-toE (y ∷ ys)
cofP-toE (ψ u (y ∷ ys))  =
  trans (cong (E.cofA (E.natT u)) (cof-toE (y ∷ ys))) (cofA-toE u (cof (y ∷ ys)))
cofP-toE (ψ zero [])    = refl
cofP-toE (ψ (suc μ) []) =
  trans (cong (E.cofψ0 (E.natT (suc μ))) (E.cof-natT μ)) (cong E.cΩ (E.pred-natT μ))
```

## §3 前驱

**定理 `pred-toE`.** `E.pred (toE t) ≡ toE (pred t)`.

EBO 的 `pred` 用通配子句 `pred (x ∷ []) = x ∷ []` 兜底, 前面一条是 `pred (𝟏 ∷ [])`; 对 `ψ (natT u) b ∷ []`, 匹配先看下标是否为 `[]`, 而 `natT u` 对变量 `u` 卡住. 所以证明对 $u$ 分情况, 每种情况两边都定义性地相等. 镜像的 `pred` 把这几条拆成互不重叠的子句 (Omega1 §4), 两边的值逐条相同, 包括哑值 (非后继的主项返回自身).

```agda
pred-toE : ∀ t → E.pred (toE t) ≡ toE (pred t)
pred-toE []                         = refl
pred-toE (x ∷ y ∷ ys)               = cong (toEP x ∷_) (pred-toE (y ∷ ys))
pred-toE (ψ zero    (y ∷ ys) ∷ [])  = refl
pred-toE (ψ (suc u) (y ∷ ys) ∷ [])  = refl
pred-toE (ψ zero    [] ∷ [])        = refl
pred-toE (ψ (suc μ) [] ∷ [])        = refl
```

## §4 Ω-基本列与 γ-链

**定理 `fsΩ-toE`.** 对每个镜像项 $t$ 与每个 $\eta$, `E.fsT (toE t) (toE η) ≡ toE (fsΩ t η)`.

无前提: EBO 的裸值 `fsT` 在 `fsT↓` 不可达的分支上的哑值, 是照镜像 `fsΩ` 的哑值选的 (EBO §6). 逐条: 和; `𝟏 ∷ []` 两边给 `[]`; 正规叶 $\Omega_{\mu+1}$ 两边给 $\eta$ (EBO 侧先用 `cof-natT` 把 `fsT0` 的分派对齐到 `c1`); $\psi_u(b)$ 的分派先经 `cof-toE` 对齐 `fsT₊`, 再经 `cmp-toE` 对齐 `fsTc`, 穿透分支 (规则 5Ω) 递归. `fsT₊`/`fsTc` 的分派参数是普通值, `cong` 即可.

```agda
fsΩ-toE  : ∀ t η → E.fsT (toE t) (toE η) ≡ toE (fsΩ t η)
fsΩ₊-toE : ∀ u b c η → E.fsT₊ (E.natT u) (toE b) (trCof c) (toE η) ≡ toE (fsΩ₊ u b c η)
fsΩc-toE : ∀ u b ν m η →
           E.fsTc (E.natT u) (toE b) (E.natT ν) (trCmp m) (toE η) ≡ toE (fsΩc u b ν m η)

fsΩ-toE []                     η = refl
fsΩ-toE (x ∷ y ∷ ys)           η = cong (toEP x ∷_) (fsΩ-toE (y ∷ ys) η)
fsΩ-toE (ψ u b@(_ ∷ _) ∷ [])   η =
  trans (cong (λ c → E.fsT₊ (E.natT u) (toE b) c (toE η)) (cof-toE b))
        (fsΩ₊-toE u b (cof b) η)
fsΩ-toE (ψ zero [] ∷ [])       η = refl
fsΩ-toE (ψ (suc μ) [] ∷ [])    η =
  cong (λ c → E.fsT0 (E.natT (suc μ)) c (toE η)) (E.cof-natT μ)

fsΩ₊-toE u b c0     η = refl
fsΩ₊-toE u b c1     η = refl
fsΩ₊-toE u b cω     η = refl
fsΩ₊-toE u b (cΩ ν) η =
  trans (cong (λ m → E.fsTc (E.natT u) (toE b) (E.natT ν) m (toE η)) (cmp-toE ν u))
        (fsΩc-toE u b ν (cmp (suc ν) u) η)

fsΩc-toE u b ν lt η = cong (λ z → E.ψ (E.natT u) z ∷ []) (fsΩ-toE b η)
fsΩc-toE u b ν eq η = cong (λ z → E.ψ (E.natT u) z ∷ []) (fsΩ-toE b η)
fsΩc-toE u b ν gt η = refl
```

带证书的版本: 只要 `fsT↓` 的前提成立 (任意证据 `e`, `η<`), 它的值就是镜像 `fsΩ` 的翻译. 这里 $\eta$ 必须是翻译过来的项, 因为输出里含有 $\eta$ 本身 (正规叶 $\Omega_{\mu+1}[\eta]=\eta$).

```agda
fsT↓-toE : ∀ t η {μ} (e : E.cof (toE t) ≡ E.cΩ μ) (η< : toE η E.<ᵀ E.Ωs μ) →
           E.trm (E.fsT↓ (toE t) e η<) ≡ toE (fsΩ t η)
fsT↓-toE t η e η< = trans (E.fsT↓-trm (toE t) e η<) (fsΩ-toE t η)
```

**定理 `γ-toE`.** γ-链逐项对应: `E.γT (toE b) (E.natT ν) k ≡ toE (γ b ν k)`, 无前提; 带证书的 `γ↓` 在任意证据 `e : E.cof (toE b) ≡ E.cΩ (E.natT ν)` 下同样. $\gamma_0=\Omega_\nu$ 两边定义性相同, 归纳步是 `fsΩ-toE`.

```agda
γ-toE : ∀ b ν k → E.γT (toE b) (E.natT ν) k ≡ toE (γ b ν k)
γ-toE b ν zero    = refl
γ-toE b ν (suc k) =
  cong (λ z → E.ψ (E.natT ν) z ∷ [])
       (trans (cong (E.fsT (toE b)) (γ-toE b ν k)) (fsΩ-toE b (γ b ν k)))

γ↓-toE : ∀ b ν (e : E.cof (toE b) ≡ E.cΩ (E.natT ν)) k →
         E.trm (E.γ↓ (toE b) (E.natT ν) e k) ≡ toE (γ b ν k)
γ↓-toE b ν e k = trans (E.γ↓-trm (toE b) (E.natT ν) e k) (γ-toE b ν k)
```

## §5 ω-基本列

**定理 `fs-toE`.** 对每个镜像项 $t$ 与每个 $n$, `E.fsn (toE t) n ≡ toE (fs t n)`; 等价地 (`fsn-toE`), `E.trm (E.fsn↓ (toEP x) (toE xs) n) ≡ toE (fsn x xs n)`.

无前提: 两边的哑值 (`c0` 行给 `[]`, 正规叶给 `natT n`, 规则 5Ω 的 ℕ-截断给 $\psi_u(b[n])$) 逐条相同.

证明的结构与 `fsn↓` 的子句一一对应. 难点是 `fsn↓` 把 `cof (y ∷ ys)` 与它的 `refl` 一起传给 `fsn↓₊`/`fsn↓0`, 证书依赖于这个计算值, 不能简单地 `cong`. 用 EBO §6 的 J-对齐 `fsn₊-eq`/`fsn0-eq` 把它换成手头的等式 `cof-toE (y ∷ ys)`, 再对镜像侧的 `c` 逐情况处理 (`fsn₊-toE`); 证书在每个分支里只出现在 `dec` 字段, 不影响 `trm`. `Cmp` 参数 (规则 5/6 的分派) 不带证书, `cong` 加 `cmp-toE` 即可 (`fsnc-toE`).

各分支: 规则 4 (`c1`) 用 `rep-trm` 把 `rep↓` 的值写成 `replicate`, 再用 `pred-toE`; 规则 5ω (`cω`) 递归; 规则 6 (`gt`) 依次用 `fsT↓-trm`, `γ↓-trm`, `γ-toE`, `fsΩ-toE`; ℕ-截断 (`lt`/`eq`) 用 `fsT↓-trm`, `toE-natT`, `fsΩ-toE`; 正规叶用 `fsn0-eq` 对齐到 `c1` 后是 `natT n`.

```agda
toE-rep : ∀ u a n → toE (rep u a n) ≡ replicate n (E.ψ (E.natT u) (toE a))
toE-rep u a zero    = refl
toE-rep u a (suc n) = cong (E.ψ (E.natT u) (toE a) ∷_) (toE-rep u a n)

fs-toE   : ∀ t n → E.fsn (toE t) n ≡ toE (fs t n)
fsn-toE  : ∀ x xs n → E.trm (E.fsn↓ (toEP x) (toE xs) n) ≡ toE (fsn x xs n)
fsn₊-toE : ∀ u y ys c (be : E.cof (toE (y ∷ ys)) ≡ trCof c) n →
           E.trm (E.fsn↓₊ (E.natT u) (toEP y) (toE ys) (trCof c) be n) ≡ toE (fsn₊ u (y ∷ ys) c n)
fsnc-toE : ∀ u y ys ν (be : E.cof (toE (y ∷ ys)) ≡ E.cΩ (E.natT ν)) m n →
           E.trm (E.fsn↓c (E.natT u) (toEP y) (toE ys) (E.natT ν) be (trCmp m) n)
             ≡ toE (fsnc u (y ∷ ys) ν m n)

fs-toE []       n = refl
fs-toE (x ∷ xs) n = fsn-toE x xs n

fsn-toE x (y ∷ ys)        n = cong (toEP x ∷_) (fsn-toE y ys n)
fsn-toE (ψ u (y ∷ ys)) [] n =
  trans (E.fsn₊-eq (E.natT u) (toEP y) (toE ys) n (cof-toE (y ∷ ys)))
        (fsn₊-toE u y ys (cof (y ∷ ys)) (cof-toE (y ∷ ys)) n)
fsn-toE (ψ zero [])    [] n = refl
fsn-toE (ψ (suc μ) []) [] n =
  trans (E.fsn0-eq E.𝟏 (E.natT μ) n (E.cof-natT μ)) (sym (toE-natT n))

fsn₊-toE u y ys c0     be n = refl
fsn₊-toE u y ys c1     be n =
  trans (E.rep-trm (E.natT u) (E.pred-< (toE (y ∷ ys)) be) n)
        (trans (cong (λ a → replicate n (E.ψ (E.natT u) a)) (pred-toE (y ∷ ys)))
               (sym (toE-rep u (pred (y ∷ ys)) n)))
fsn₊-toE u y ys cω     be n = cong (λ z → E.ψ (E.natT u) z ∷ []) (fsn-toE y ys n)
fsn₊-toE u y ys (cΩ ν) be n =
  trans (cong (λ m → E.trm (E.fsn↓c (E.natT u) (toEP y) (toE ys) (E.natT ν) be m n)) (cmp-toE ν u))
        (fsnc-toE u y ys ν be (cmp (suc ν) u) n)

fsnc-toE u y ys ν be gt n =
  cong (λ z → E.ψ (E.natT u) z ∷ [])
       (trans (E.fsT↓-trm (toE (y ∷ ys)) be _)
              (trans (cong (E.fsT (toE (y ∷ ys))) (γ↓-toE (y ∷ ys) ν be n))
                     (fsΩ-toE (y ∷ ys) (γ (y ∷ ys) ν n))))
fsnc-toE u y ys ν be lt n =
  cong (λ z → E.ψ (E.natT u) z ∷ [])
       (trans (E.fsT↓-trm (toE (y ∷ ys)) be _)
              (trans (cong (E.fsT (toE (y ∷ ys))) (sym (toE-natT n)))
                     (fsΩ-toE (y ∷ ys) (natT n))))
fsnc-toE u y ys ν be eq n =
  cong (λ z → E.ψ (E.natT u) z ∷ [])
       (trans (E.fsT↓-trm (toE (y ∷ ys)) be _)
              (trans (cong (E.fsT (toE (y ∷ ys))) (sym (toE-natT n)))
                     (fsΩ-toE (y ∷ ys) (natT n))))
```

Omega1 §7.3 的样例核对现在是 `fs-toE` 的特例. 例如 $\varepsilon_0[3]$ 与 $\psi_0(\psi_1(\Omega_1))[3]$:

```agda
private
  εₜ bh : T
  εₜ = ψ 0 (ψ 1 [] ∷ []) ∷ []
  bh = ψ 0 (ψ 1 (ψ 1 [] ∷ []) ∷ []) ∷ []

  _ : E.fsn (toE εₜ) 3 ≡ toE (fs εₜ 3)
  _ = fs-toE εₜ 3

  _ : E.fsn (toE bh) 3 ≡ toE (fs bh 3)
  _ = refl
```

## §6 推论: 单射与封闭性

**`toE` 是单射**, 所以镜像表记就是 EBO 的一个子表记 (下标为自然数的部分), 不是商.

```agda
natT-inj : ∀ m n → E.natT m ≡ E.natT n → m ≡ n
natT-inj zero    zero    e = refl
natT-inj zero    (suc n) ()
natT-inj (suc m) zero    ()
natT-inj (suc m) (suc n) e = cong suc (natT-inj m n (proj₂ (∷-injective e)))

ψ-inj : ∀ {u v a b} → E.ψ u a ≡ E.ψ v b → (u ≡ v) × (a ≡ b)
ψ-inj refl = refl , refl

toE-inj  : ∀ s t → toE s ≡ toE t → s ≡ t
toEP-inj : ∀ x y → toEP x ≡ toEP y → x ≡ y
toE-inj []       []       e = refl
toE-inj []       (_ ∷ _)  ()
toE-inj (_ ∷ _)  []       ()
toE-inj (x ∷ xs) (y ∷ ys) e =
  cong₂ _∷_ (toEP-inj x y (proj₁ (∷-injective e))) (toE-inj xs ys (proj₂ (∷-injective e)))
toEP-inj (ψ u a) (ψ v b) e =
  cong₂ ψ (natT-inj u v (proj₁ (ψ-inj e))) (toE-inj a b (proj₂ (ψ-inj e)))
```

**像的内在刻画.** `NS t`: EBO 项 $t$ 的下标 (遗传地) 都是 `natT k`. 它恰好刻画 `toE` 的像.

```agda
data NS  : E.T → Set
data NSP : E.PT → Set
data NS where
  ns[] : NS []
  ns∷  : ∀ {x xs} → NSP x → NS xs → NS (x ∷ xs)
data NSP where
  nsψ : ∀ k {a} → NS a → NSP (E.ψ (E.natT k) a)

NS-toE  : ∀ t → NS (toE t)
NSP-toE : ∀ x → NSP (toEP x)
NS-toE []       = ns[]
NS-toE (x ∷ xs) = ns∷ (NSP-toE x) (NS-toE xs)
NSP-toE (ψ u a) = nsψ u (NS-toE a)

Im : E.T → Set
Im t = Σ T λ t₀ → toE t₀ ≡ t

NS→Im  : ∀ {t} → NS t → Im t
NSP→Im : ∀ {x} → NSP x → Σ P λ x₀ → toEP x₀ ≡ x
NS→Im ns[] = [] , refl
NS→Im (ns∷ p w) with NSP→Im p | NS→Im w
... | x₀ , refl | t₀ , refl = x₀ ∷ t₀ , refl
NSP→Im (nsψ k w) with NS→Im w
... | a₀ , refl = ψ k a₀ , refl
```

**封闭性.** 下标为 `natT` 的 EBO 项对 `pred`, `fsn` (即 `fsn↓` 的值), `fsT` 与带证书的 `fsT↓`, `γT`/`γ↓` 封闭, 输出的下标仍是 `natT`. 证明: 取原像, 用对应的翻译定理把输出写成某个镜像项的翻译. 这也说明这个子集上的共尾度只会是 `c0`, `c1`, `cω`, `cΩ (natT μ)` (`NS-cof`).

```agda
NS-cof : ∀ {t} → NS t → Σ Cof λ c → E.cof t ≡ trCof c
NS-cof w with NS→Im w
... | t₀ , refl = cof t₀ , cof-toE t₀

NS-pred : ∀ {t} → NS t → NS (E.pred t)
NS-pred w with NS→Im w
... | t₀ , refl = subst NS (sym (pred-toE t₀)) (NS-toE (pred t₀))

NS-fsn : ∀ {t} → NS t → ∀ n → NS (E.fsn t n)
NS-fsn w n with NS→Im w
... | t₀ , refl = subst NS (sym (fs-toE t₀ n)) (NS-toE (fs t₀ n))

NS-fsn↓ : ∀ {x xs} → NS (x ∷ xs) → ∀ n → NS (E.trm (E.fsn↓ x xs n))
NS-fsn↓ w n = NS-fsn w n

NS-fsT : ∀ {t η} → NS t → NS η → NS (E.fsT t η)
NS-fsT w wη with NS→Im w | NS→Im wη
... | t₀ , refl | η₀ , refl = subst NS (sym (fsΩ-toE t₀ η₀)) (NS-toE (fsΩ t₀ η₀))

NS-fsT↓ : ∀ {t μ} (e : E.cof t ≡ E.cΩ μ) {η} (η< : η E.<ᵀ E.Ωs μ) →
          NS t → NS η → NS (E.trm (E.fsT↓ t e η<))
NS-fsT↓ {t} e η< w wη = subst NS (sym (E.fsT↓-trm t e η<)) (NS-fsT w wη)

NS-γT : ∀ {β} → NS β → ∀ ν k → NS (E.γT β (E.natT ν) k)
NS-γT w ν k with NS→Im w
... | β₀ , refl = subst NS (sym (γ-toE β₀ ν k)) (NS-toE (γ β₀ ν k))

NS-γ↓ : ∀ {β} ν (e : E.cof β ≡ E.cΩ (E.natT ν)) k → NS β → NS (E.trm (E.γ↓ β (E.natT ν) e k))
NS-γ↓ {β} ν e k w = subst NS (sym (E.γ↓-trm β (E.natT ν) e k)) (NS-γT w ν k)
```

## §7 结论与边界

**已证** (全部 `--safe --without-K`, 无公设、无洞、无停机编译指示). 记镜像表记 (Omega1 §4) 的项为 `T`, 翻译 `toE : T → E.T` 把 $\psi_u(a)$ 换成 $\psi_{\mathtt{natT}\,u}(\mathtt{toE}\,a)$, `trCof` 把 `cΩ μ` 换成 `E.cΩ (E.natT μ)`. 对**一切**镜像项 (下标为任意自然数, 不要求 $\le1$, 不要求标准形):

| 定理 | 陈述 | 前提 |
|---|---|---|
| `cmp-toE` | `E.cmpᵀ (E.sucT (E.natT ν)) (E.natT u) ≡ trCmp (cmp (suc ν) u)` | 无 |
| `cof-toE` | `E.cof (toE t) ≡ trCof (cof t)` | 无 |
| `pred-toE` | `E.pred (toE t) ≡ toE (pred t)` | 无 |
| `fs-toE` | `E.fsn (toE t) n ≡ toE (fs t n)` | 无 |
| `fsn-toE` | `E.trm (E.fsn↓ (toEP x) (toE xs) n) ≡ toE (fsn x xs n)` | 无 |
| `fsΩ-toE` | `E.fsT (toE t) (toE η) ≡ toE (fsΩ t η)` | 无 |
| `fsT↓-toE` | `E.trm (E.fsT↓ (toE t) e η<) ≡ toE (fsΩ t η)` | `fsT↓` 自身的前提 `e`, `η<` (任意证据) |
| `γ-toE` | `E.γT (toE b) (E.natT ν) k ≡ toE (γ b ν k)` | 无 |
| `γ↓-toE` | `E.trm (E.γ↓ (toE b) (E.natT ν) e k) ≡ toE (γ b ν k)` | `γ↓` 自身的前提 `e` |
| `toE-inj` | `toE s ≡ toE t → s ≡ t` | 无 |

推论: `NS t` (下标遗传地为 `natT k`) 恰是 `toE` 的像 (`NS-toE`, `NS→Im`); 这个子集对 `E.pred`, `E.fsn`/`E.fsn↓`, `E.fsT`/`E.fsT↓`, `E.γT`/`E.γ↓` 封闭, 其上的共尾度都形如 `trCof c` (`NS-cof`). 于是 Omega1 §7.3 的 12 个样例核对现在是 `fs-toE` 的实例, 而 Omega1 的对应定理 (树 ↔ 镜像) 与本文 (镜像 ↔ EBO) 复合, 就是树 ↔ EBO 在下标 $\le1$ 片段上的对应.

**为什么不需要前提.** 镜像表记的哑值是照 EBO 抄的 (`fs` 的 `c0` 行、正规叶的 `natT n`、规则 5Ω 的 ℕ-截断), 两边逐条相同. EBO 的 Ω-基本列 `fsT↓` 在不合法输入上没有值; 它的裸值 `fsT` (EBO §6) 的哑值是自由选择, 选成了与镜像 `fsΩ` 相同. 若换一种哑值, `fsΩ-toE` 就要加前提 "`cof t ≡ cΩ μ`" (合法输入), 而 `fsT↓-toE` 不受影响.

**证明手法.** (1) `cmpᵀ` 的 `with` 辅助函数在具体的 $\mathbf 1$ 上归约, `cmpᵀ (natT m) (natT n)` 对 $m,n$ 归纳即可. (2) `fsn↓` 把 `cof b` 连同 `refl` 传给辅助函数, 证书依赖于它; 用 J-对齐 (`fsn₊-eq`, `fsn0-eq`: 对等式匹配 `refl`) 换成 `cof-toE` 的证据, 再按镜像侧的 `Cof` 逐情况证 (`fsn₊-toE`), 证书只在 `dec` 字段, 不进入陈述. (3) EBO 的 `pred` 用通配兜底子句, 对 `natT u` 卡住, 证明对 $u$ 分情况. (4) `fsT↓`/`γ↓` 先经 `fsT↓-trm`/`γ↓-trm` 化为裸值, 翻译定理全部在裸值上陈述.

**边界.**

- 本文只覆盖**下标为自然数**的 EBO 项, 即 $\psi_0(\Omega_\omega)$ 以下. EBO 的 `cofψ0` 的 `cω`/`cΩ` 分支 (奇异 $\Omega_u$, $u$ 为极限) 与 `fsn↓0`/`fsT↓0` 的对应分支在像里从不出现; 下标为 $\Omega_\omega$, $\Omega_{\Omega}$ 等的项没有镜像. 树侧要到达这些项需要对角 (下标层的极限 $\Omega_\lambda[n]=\Omega_{\lambda[n]}$, 以及下标本身是 Ω-共尾时 $\Omega_u[\eta]=\Omega_{u[\eta]}$), 那是交替路线的下一阶段; 届时镜像表记的下标类型要从 ℕ 换成可数下标或项本身, 本文的 `cmp-toE`/`cof-toE` 需相应地换成下标翻译与 `cmpᵀ` 的交换引理.
- 翻译定理是**逐字**相等, 不涉及标准形. 两边在非标准项上同样算出同样的值; 至于这些值有没有序数意义, 由树侧的对应定理 (Omega1 的前提 `W`, `Top₀`) 与 EBO 的标准形理论 (未做, 见 EBO §9) 决定.
- 镜像的规则 5Ω ℕ-截断与正规叶的 `natT n` 是哑值, 本文只证明两边哑值相同, 不赋予它们意义.
- Omega1 的树侧定理只覆盖下标 $\le1$; 本文的翻译虽对全部自然数下标成立, 树 ↔ EBO 的复合目前也只到 Bachmann–Howard 序数.
