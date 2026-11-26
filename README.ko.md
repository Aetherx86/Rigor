# Rigor: 안전한 Rust로 구현된 독립형 Lean 4 증명 검증 커널

Rigor는 `#![forbid(unsafe_code)]` 및 외부 의존성 0개의 순수 Rust로 작성된 Lean 4 (Calculus of Inductive Constructions) 독립 증명 검증 커널입니다. `lean4export` NDJSON 및 텍스트 형식을 스트리밍 파싱하여 모든 공리·정의·정리·귀납 타입·재귀자를 독자적으로 재검증합니다.

English documentation: [`README.md`](./README.md) | Live WASM demo: <https://omakasekim.github.io/rigor/>

## 주요 기능 (v0.3.0)

- **최소 신뢰 커널 (`crates/kernel`, ~2,700 LOC)**: 16바이트 해시-콘싱 아레나, 우주 레벨 및 불평등 검사, 엄격한 양의성(strict positivity), 큰 제거(large elimination), 몫 타입(quotient), 증명 무관성, eta 변환, `Nat`/문자열 리터럴 및 병렬 선언 검증.
- **공리 감사 및 의존성 경로 추적 (`crates/parser`)**: 전이적 공리 의존성(`--audit`, `#print axioms` 동등), `--forbid-sorry`/`--allow-axioms` 정책 검증, 최단 의존성 증인 경로 추적(`--why`), 역의존성(`--rdeps`), 선언 목록 필터링(`--list`).
- **WebAssembly 브라우저 엔진 (`web/`)**: `check(input)`, `audit(input, decl)`, `why(input, from, to)`, `version()` 내보내기.

## 빌드 및 실행

```bash
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace --release
cargo build --release -p rigor-bench
./target/release/rigor-bench --version
```

## 라이선스

MIT License — 자세한 내용은 [`LICENSE`](./LICENSE)를 참고하세요.
