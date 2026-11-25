# B9N · 整棵 Y 1 在一次更新处是否已经成立

请独立检验 `First = Match (Y 1) (chainW 1)`，与 B9A 保持同一参照。全程中文，模型 Opus 5.5。先读仓库根 `AGENTS.md`、工程手册 §4 及[主审指令 02](../指令-02.md)。协调者提供公共目录；独立收到本简报时可先运行[公共准备段](00-协调简报.md)。在 `$B9_RUN/B9N` 写纯 Agda，新模块前缀 `B9Upper`。

**首试交付 `no-first : First → ⊥`，也接受带两个消费者闭实例的 `first : First`。** 第八批否定了冻结初态。主审补证的是较小参照 `X₀` 在一次更新处成立而在初态不成立。`B8PairMain.no-merge` 只排除一个描述，尚没有关于整个 `First` 的否定。

1. 以 `YiLAB8Split.out 1` 为右端。先试 `out 1 ≼ LV.ψ⁰ X₀`。现有 `B8PairMain.c-add₀` 给反向；若上界成立，配合 `B8PairMain.X₀≺Y1`，用已编译的 `refute-at {X = Y 1} {n = 1}` 即可否定所有允许的共同描述。B8N 的 `fold-up` 只管初态；请从 `chainW1-shape` 展开本次更新的累加与 `ex`，核对上界是否真的保持。初态的精确上界可作基例。
2. 可以更换上界 H。所需的两条是 `out 1 ≼ H` 与 `LV.suc H ≼ LV.ψ⁰ (Y 1)`，同一 H 且前提可满足。`B8FreezeMain.Y1-big` 可帮助在 Level 一侧挑选阈值。另一种写法可直接反驳同一个闭消费者目标。若编出 `First` 正例，交四个字段和两个出口，记录是哪一步推翻了上界判断。
3. 对一份描述的逐点比较失败，不排除别的描述；指数消费亦不能由被加项消费者的否定自动判断。若两种写法都受阻，列出最后已编译的具体上界、尚缺的上界保持行、它实际经过的 W4 参数以及一个非空实例。先纸面后编译，每路新代码约 1200 行，可换一次写法。对第九批整条路线的裁定交主审。

在仓库根执行，按入口实名替换文件名：

```sh
agda +RTS -M6G -RTS --library-file="$B9_RUN/libraries" -i src -i probes -i "$B9_RUN/common" -i "$B9_RUN/B9N" "$B9_RUN/B9N/B9UpperMain.agda" > "$B9_RUN/B9N/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

沿用公共 OPTIONS，一次一个 Agda；仓库、W4、公共源码只读。第 4 层若有经典条件，必须作参数并标明具体用途。回报列签名、量化域、前提与实例、源码、冷编退出码和仍开放的命题。把结果交给协调者复核，无须等待构造路。
