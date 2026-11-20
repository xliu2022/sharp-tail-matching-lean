# 锐尾概率与大匹配定理的 Lean 形式化

本项目形式化了 Cheng Chi、Shuang Sun、Yan Wang 的锐尾概率定理和大匹配情形的 Erdős 匹配定理，证明组织参考了 [paper/](paper/) 中的详细稿。稿件中的全部证明由 GPT 在他们原有论证的基础上简化和展开，并非独立于他们工作的证明。形式化作者为 Heng Li、Xizhi Liu，负责人为 Xizhi Liu。仓库采用 Apache-2.0 许可证；数学来源和依赖保留各自的许可证。

九项主声明都有完整证明。2026 年 11 月 20 日，本机从干净目录完成了 macOS 构建；59 项声明的公理审计仅发现三个标准 Lean 公理，导出的证明项也通过了 Lean、NanoDa 和 con-ron 检查。结果见 [verification/RESULTS.json](verification/RESULTS.json) 和相应日志。受保护 Comparator 需要 Linux namespaces，未能在 macOS 原生环境运行，故尚未通过 Palomar 的正式机械验收。本项目尚未向 Palomar 提交或登记。

English guide: [README.md](README.md).

## 已形式化的数学结论

对于每个固定整数 $k\ge3$，存在 $s_0(k)$，使得对所有 $s\ge s_0(k)$ 和 $n\ge k(s+1)$，每个整数匹配数至多为 $s$ 的 $n$ 顶点 $k$ 一致超图都满足

$$|H|\le\max\left\{\binom nk-\binom{n-s}k,\binom{k(s+1)-1}k\right\}.$$

等号分类完整：超图必须是完整 $s$-覆盖，或 $k(s+1)-1$ 个顶点上的完全 $k$-图加孤立点，并且该构造的边数达到两个候选值的较大者。候选值相同时允许两种构造。这个匹配结论的范围是固定 $k\ge3$、$s$ 充分大。

概率结论适用于非负实数上的任意 Borel 概率分布。给定 $k\ge1$ 和 $0\le x\le1/k$，在均值约束 $\mathbb E X\le x$ 下，$k$ 个独立同分布样本之和至少为一的最大概率为

$$\max\{1-(1-x)^k,(kx)^k\}.$$

当 $x>1/k$ 时最大值为一。达到上界的分布、全部极值分布及各个边界情况都已形式化，没有有限支撑或有界支撑的额外限制。

[Challenge.lean](Challenge.lean) 是只导入 Mathlib 的独立陈述文件。Comparator 配置包含以下九个目标，命名空间均为 `SharpTailMatching`：

| 声明 | 内容 |
| --- | --- |
| `large_matching_bound` | 大匹配情形的精确边数上界 |
| `large_matching_equality` | 极值超图的完整分类 |
| `sharp_tail_bound` | 一般概率分布的锐尾上界 |
| `sharp_tail_attained` | 所有允许参数下的上界取到 |
| `critical_mean_exists_unique` | 两个候选尾概率的唯一正交点 |
| `sharp_tail_equality` | 非平凡均值区间的全部极值分布 |
| `zero_mean_iff` | 零均值分布的分类 |
| `one_sample_equality` | 单样本的完整等号分类 |
| `tail_eq_one_iff` | 尾概率等于一的分布分类 |

Challenge 中的九个 `sorry` 是独立陈述有意保留的占位。Solution 不导入 Challenge；证明库没有证明占位、自定义公理或 `native_decide`。打包时保留了全部数学声明、定义和证明源码。

## 阅读入口

- [Probability/Main.lean](SharpTailMatching/Probability/Main.lean)：锐尾概率定理及等号分类。
- [Matching/ApproximateCover.lean](SharpTailMatching/Matching/ApproximateCover.lean)：由正则性、有限对偶及取整证明近似分数覆盖。
- [Matching/Stability.lean](SharpTailMatching/Matching/Stability.lean)：超图稳定性。
- [Matching/Main.lean](SharpTailMatching/Matching/Main.lean)：匹配主定理及完整等号分类。
- [paper/main.pdf](paper/main.pdf)：详细论文；LaTeX 源码、图和代数证书随附在 `paper/` 中。

## 构建与复核

项目固定使用 Lean 4.35.0-rc2 和 Mathlib 提交 `065356127b1dc0016f66b7283ce0ce2c4055aa55`。安装 Lean/Lake、Python 3 和 Ruby 后，在仓库根目录运行：

```bash
lake exe cache get
bash verify.sh
```

这会检查源码格式、元数据、完整构建、59 项声明及其公理依赖，并把匹配数、二项式边数和等号结构展开为普通有限集合陈述后核验两项匹配目标。元数据脚本检查 starter 格式字段和占位内容，官方完整元数据验证仍由 Palomar 流水线执行。

要重新导出证明项并运行三个内核：

```bash
bash verify.sh --kernels
```

新日志和报告写入 `.lake/verification/`，已记录的 `verification/` 证据保持不变。证明导出文件可由上述命令重新生成，源码包不包含大型证明导出文件、工具链或 Mathlib 缓存。

在支持 `bubblewrap` 隔离的 Linux 环境中，还可运行：

```bash
bash verify.sh --comparator
```

此命令保持隔离开启，只允许 `propext`、`Quot.sound`、`Classical.choice`。附带的 Linux CI 会执行源码、元数据、构建、公理和独立内核检查；本次打包没有触发远程 CI。

## Palomar 提交

把本文件夹的内容作为 GitHub 仓库根目录，连同隐藏的 `.github/` 和 `.gitignore` 一起提交。可以运行已有的 **Palomar full mechanical preflight** 手动工作流；它以 `mode: full` 调用固定版本的官方流水线。需要取得固定公开提交的完整机械报告 `status: pass`，再进行提交。

提交入口为 https://submit.palomar-registry.org/。填写公开仓库和完整 40 位提交 SHA，使用根目录的 `comparator.json`、`formalization.yaml`。官方审查和是否登记是后续步骤；具体以[当前提交要求](https://palomar-registry.org/how-to-submit)为准。

目录组织参考 [improved-sidorenko-lean](https://github.com/xliu2022/improved-sidorenko-lean/tree/ba6f109bf01436ca15e55fdf5d35dbea85ffd9c9)，来源记录见 [verification/PROVENANCE.json](verification/PROVENANCE.json)。在 `paper/` 中运行 `latexmk -pdf main.tex` 可编译论文。
