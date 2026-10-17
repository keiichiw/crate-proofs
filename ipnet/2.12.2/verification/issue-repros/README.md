# ipnet の問題と Aeneas の機能不足：再現資料

対象は **ipnet 2.12.2**（commit `13c5c5873c02127679b1e8e64b538e4e36942640`）。
調査日 2026-10-16。公開・issue 作成・PR 送信はしていない。
Rust の実行反例と、検証ツールが処理できないことを区別する。
以下のコマンドは `/Users/keiichiw/workspace/crate-proofs` を作業ディレクトリとする。

## 1. ipnet 自体の問題

| ID | 現象 | 判定 | 最小入力 |
|---|---|---|---|
| IPNET-001 | IpNet の schema が正しく serialize した IPv4 を拒否 | 確認済み不具合 | `0.0.0.0/0` |
| IPNET-002 | IPv6 schema が deserialize できない文字列を受理 | 公式の Serde 互換性目標から schema 不具合と判断（根拠は追加調査） | `a/64` |
| IPNET-003 | `heapless` feature 単独では一時的なヒープ確保が発生 | 確認済み不具合 | IPv4 値1個と非割当 serializer |

### IPNET-001 / IPNET-002：schema

[最小 Rust プログラム](ipnet/schema-minimal.rs) は20行で、実ライブラリから
schema と serialize 結果を生成する。[検査コード](ipnet/schema-minimal.py) は
生成された schema を jsonschema で評価する。正規表現をコピーした模擬実装ではない。
[独立 Cargo.toml](ipnet/Cargo.toml) と lockfile を同梱。

```sh
cargo +1.91.1 run --offline --locked \
  --manifest-path ipnet/2.12.2/verification/issue-repros/ipnet/Cargo.toml \
  > /tmp/ipnet-schema-minimal.json
ipnet/2.12.2/.tools/schema-python/bin/python \
  ipnet/2.12.2/verification/issue-repros/ipnet/schema-minimal.py \
  < /tmp/ipnet-schema-minimal.json
```

Python 環境は既存の `verification/bugs/schema-repro/requirements.txt`
（jsonschema 4.25.1）を使う。Rust schema 依存は schemars 0.8.22 / 1.2.1。
両方で次の結果になる。

- `0.0.0.0/0` は parse・serialize できるが、IpNet schema は拒否。
  IPv4 と広すぎる IPv6 pattern の両方に一致し、`oneOf` の「ちょうど1つ」条件に反する。
- `a/64` は IPv6 schema に通るが、Ipv6Net の deserialize はエラー。
  公式の Serde 互換性目標と導入意図から schema 不具合と判断する。
  全入力の完全一致の明示保証までは確認していない。

修正方針：IPv4/IPv6 schema を適切に分離する。`oneOf` を `anyOf` に変えるだけでは
IPNET-002 の過剰受理は解消しない。埋込み IPv4 を含む IPv6 表記の扱いも必要。
詳細・過去の反例：[既存 findings](../bugs/README.md)。

### IPNET-003：heapless の feature 分岐

[実行可能な最小ハーネス](../bugs/heapless-feature-repro/src/main.rs) は、
IPv4 値1個を serialize し、呼出し中の allocation/reallocation を数える。
Serializer の必須メソッドの実装は含むが、`serialize_str` 自体は確保せず、
serde の既定 `collect_str` をそのまま利用する。parse と結果表示は計測区間外。

```sh
cargo +1.91.1 run --offline --locked \
  --manifest-path ipnet/2.12.2/verification/bugs/heapless-feature-repro/Cargo.toml \
  --features heapless
cargo +1.91.1 run --offline --locked \
  --manifest-path ipnet/2.12.2/verification/bugs/heapless-feature-repro/Cargo.toml \
  --features legacy
```

期待：どちらも ipnet の一時文字列用の確保は0回。
実際：同一の `255.255.255.255/32` が出力され、heapless は3回、legacy は0回。
`--bin ipv6` を追加すると43バイトの IPv6 表記でも4回対0回。
回数の厳密値は実行環境依存であり、問題は heapless 側の正の確保回数。
原因は `ipnet_serde.rs` の buffer 分岐が legacy `ser_as_str` だけを条件にしていること。

[修正候補の差分](../heapless-candidate/cfg.patch) は4つの cfg guard を修正する。
[候補の検証結果](../heapless-candidate/results.md) は native 検査と条件付き数学証明を
含むが、Serialize 本体の形式証明完了を意味しない。

### ipnet 反例の一括再現

```sh
python3 ipnet/2.12.2/verification/issue-repros/ipnet/run.py
```

成功終了は「既知の問題が再現した」を意味する。「修正済み」のテストではない。
[再実行の証跡](ipnet/evidence.json) にコマンド・終了コード・ソースとログのハッシュを記録。
無効 prefix に対する raw subnet iterator の panic は、既知の領域外挙動として
[別記録](../bugs/subnets-domain-repro/README.md)に残し、新規の算法バグには数えない。

## 2. Aeneas 側の機能不足

対象は Aeneas `8e62dc3dc765602833c86b68dceb18a475a50a8f`、
Charon `08d7c9d50144bd84848212c24701253585e90d1f`、抽出 Rust nightly-2026-09-17、
Lean 4.35.0。ローカル互換パッチも存在するため、未修正 upstream 全般や最新版への
主張ではない。各再現資料のコマンド・パッチ・バイナリ識別情報を参照。

### AENEAS-001：可変 trait object への変換

修正候補の `fmt::write(&mut buf, format_args!("{self}"))` で
`&mut heapless::String<N>` → `&mut dyn fmt::Write` の変換を扱えない。
期待：呼出し後の buffer 更新も保持した意味を生成する。
実際：Aeneas の変換が失敗し、Serialize 本体の証明に進めない。
IPv4・IPv6 とも実装から確認済み。optimized MIR と fmt::write の追加抽出でも解消しない。

[縮小再現パッケージ](aeneas/)と、実 ipnet に対する
[新規抽出の証跡](../heapless-candidate/evidence/latest/result.json)を参照。
shared reference や identity cast に置換すると更新を失うため、正当な回避策にならない。

### AENEAS-002：借用引数を変更する FnOnce の型と更新値

実 parser の callback は Parser の可変状態を変更する。生成された呼出し側は
`(Option T, Parser)` を必要とするが、FnOnce のメソッド型は `Option T` だけになり、
Lean の型検査が失敗する。期待：可変引数の更新を trait 宣言・instance・呼出し側で整合させる。
更新を捨てると parser の消費位置・rollback の意味が失われる。

[詳細な過去の再現](../blockers/ipv4-parser-callback/README.md)には、先行する抽出障害を
通過するための実験パッチ、生成テキスト、失敗ログ、monomorphization の試行を保存。
その実験パッチは現在の検証環境には適用されていない。
今回の独立した `next_ascii` 最小例では、現行の固定ツールと既存の互換パッチだけで
同じ FnOnce 型不整合を再現できた。parser 用実験パッチは不要。
[コード・コマンド・失敗ログ](aeneas/README.md)を同梱する。

### AENEAS-003：Iterator trait signature 処理の internal error

独立した `dst.extend(src.iter().copied())` の最小例は、Charon 抽出に成功するが、
Aeneas の Iterator trait signature 処理で internal error になる。
[再現パッケージとログ](aeneas/README.md)を参照。これは次項の実 aggregate における
Vec 内部への到達より手前の別現象であり、同じ原因だとは断定しない。

### 外部ライブラリモデルの不足（上記3件と別分類）

- **Vec::extend / collect**：aggregate を実際に抽出すると SpecExtend →
  extend_desugared → capacity/reserve/raw-pointer write 等へ進み、必要な外部モデルが未整備。
  [IPv4/IPv6 の4つの絞り込み再現・ログ](../blockers/aggregate-extend/README.md)。
- **Formatter の出力状態**：現在の外部 Formatter モデルでは出力テキストを保持しないため、
  Display の本体が抽出できても文字列の正確さを証明できない。
  この Display の観測は過去のローカル診断であり、今回の新規実行ログには含めない。
  [候補の現状](../heapless-candidate/README.md)を参照。
- **sort / last_mut / iterator adapters**：aggregate に必要な外部契約や
  backward update の接続が未完了。[必要な契約と観測済み境界](../ipv4-aggregate-boundaries.md)。

これらは ipnet の実行反例でも、すべて独立した Aeneas バグでもない。
明示的な外部仮定を使う場合も、状態更新・callback・エラーを保持する接続が必要。
[外部仮定一覧](../heapless-candidate/assumptions.md)を参照。
過去にローカル修正済みの名前衝突・inherent matcher 等は、今回の未解決問題には混ぜない。

## 再現パッケージの入口

```sh
# 既知の ipnet 反例が再現されれば成功
python3 ipnet/2.12.2/verification/issue-repros/ipnet/run.py
# 期待した Aeneas/Lean の失敗を検出できれば成功
bash ipnet/2.12.2/verification/issue-repros/aeneas/reproduce.sh
```

いずれもこのリポジトリの固定ツール・依存キャッシュを前提にする。
Aeneas の再現コードは ipnet に依存しない独立 Cargo workspace。
外部への報告時は、その README のバージョン・ローカルパッチ情報も添付する。

## 仕様・既存 issue の追加調査

[2026-10-16 の確認結果](upstream-review.md)に schema の分類根拠、
Aeneas の既存 issue/PR、未実装と実装不具合の区別を記録した。
