# 探针

小而决定性的 Agda 实验。`.agda` 是通过的，纳入 `tools/check-src.sh`；`.agda.txt` 是**故意不通过**的，存为文本以免破坏构建，文件头写着 Agda 2.8.0 `--safe` 的原始报错。

| 文件 | 问的问题 | 结果 | 结论 |
|---|---|---|---|
| `MahloIR.agda.txt` | Setzer 的**内部** Mahlo 宇宙 V（`û : ((a:V)→(T a→V)→V) → … → V`）能否在 `--safe` 定义？ | `NotStrictlyPositive`：V 在 `û` 的箭头左边 | 不能。沿「先定义 V 再归纳」证良序的路在 `--safe` 走不通（§122.2） |
| `SuperIR.agda` | 对一个**给定** `F : Set → Set` 封闭的宇宙呢？ | 通过 | 超宇宙式闭包是普通 IR |
| `MahloParam.agda` | Definition 4.3 的 `Û_{f,g}`／`s`／`Res0`／`Res1` 与两条计算方程，取 **V := `Set`、s := `T`**，对给定 (f,g) 参数化，能否定义？ | **通过** | Setzer 良序证明的唯一 Mahlo 步骤（Lemma 5.10）只需要这个形状——**路线 C 的可行性依据**（§123.4） |
| `IRUniv.agda.txt` | 对**全部** IR 代码同时封闭的单一宇宙 𝕌？ | 终止检查失败：`𝕋` 作为参数传给解码器 | 不能直接做；但路线 C 不需要它 |

重跑：`agda --safe Probe/MahloParam.agda`；失败探针把 `.txt` 去掉后跑，应复现文件头的报错。
