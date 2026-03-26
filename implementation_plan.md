# Program Verifier Implementation Plan

이 문서는 사용자가 직접 `engine/verifier.ml`을 작성하여 부분 정당성 검증기(Partial Correctness Verifier)를 완성하기 위한 단계별 구현 계획입니다. 직접 실행해 보실 수 있도록 각 단계를 기능 단위로 쪼개어 설명합니다.

## User Review Required

본 계획은 과제의 전형적인 호어 논리(Hoare Logic) 및 약한 사전조건(Weakest Precondition, WP) 기반의 검증기 구현 방식을 따릅니다.
만약 수업이나 과제에서 요구한 **특정 WP/VC 연산 규칙**(예: 루프 불변식을 처리하는 방식)이나 **사용해야 하는 자료구조**가 명시되어 있다면 이 계획을 수정해야 할 수 있습니다. 꼭 확인해 주세요!

## Proposed Changes

### [Engine]

#### [MODIFY] [verifier.ml](file:///home/kyle/LogicVerify/engine/verifier.ml)

**Step 1. Z3 SMT 표현식 변환기 구현 (Expressions)**
- `Syntax.exp` (Dafny의 수식 AST)를 `Smt.Expr.t` (Z3 OCaml 바인딩의 수식)로 변환하는 함수 `trans_exp : Syntax.exp -> Smt.Expr.t`를 작성해야 합니다.
- `utils/smt.ml`의 `Smt.Expr` 모듈이 제공하는 `create_add`, `create_eq`, `of_int` 등의 헬퍼 함수를 활용합니다.
- 변수는 `Smt.Expr.create_var`를 사용하여 Z3 변수로 매핑합니다. (이때 각 변수의 타입 환경을 유지하여 알맞은 Z3 Sort(int, bool 등)로 생성해야 합니다.)

**Step 2. Z3 SMT 논리식 변환기 구현 (Formulas)**
- `Syntax.fmla`를 `Smt.Fmla.t`로 변환하는 함수 `trans_fmla : Syntax.fmla -> Smt.Fmla.t`를 작성합니다.
- `Smt.Fmla` 모듈의 `create_and`, `create_or`, `create_imply`, `create_forall` 등을 사용합니다.

**Step 3. 약한 사전조건(Weakest Precondition, WP) 생성기 구현**
- 가장 중요한 단계입니다. 문장(`stmt`)과 사후조건(`fmla`)을 입력받아 사전조건(`fmla`)을 반환하는 함수 `wp : Syntax.stmt -> Syntax.fmla -> Syntax.fmla` (혹은 반환값을 곧바로 Z3 객체로 다루는 `Smt.Fmla.t`)를 구현합니다.
- 핵심 규칙:
  - **Skip**: `wp(S_skip, Q) = Q`
  - **Assign**: `wp(S_assign(x, e), Q) = Q[e/x]` (`Syntax.replace_fmla` 활용)
  - **Sequence**: `wp(S_seq(s1; s2), Q) = wp(s1, wp(s2, Q))`
  - **If**: `wp(S_if(c, s1, s2), Q) = (c => wp(s1, Q)) /\ (~c => wp(s2, Q))`
  - **While(Loop)**: 부분 정당성을 다루므로, Loop Invariant(항진식 $I$)를 사용합니다. 일반적인 검증 조건 생성 시 `wp(while, Q)`은 복잡해질 수 있으므로, 루프 불변식이 초기화 시 만족되는가($P \Rightarrow I$), 루프 조건 참일 때 유지되는가($I \land C \Rightarrow wp(body, I)$), 루프가 끝났을 때 사후조건을 만족하는가($I \land \neg C \Rightarrow Q$)에 대한 **Verification Conditions(VCs)**를 수집하는 식으로 구현을 다듬을 필요가 있습니다.

**Step 4. 검증 조건(Verification Condition, VC) 검사 (Valid 여부 판별)**
- 각 메서드(`mthd`)에 대해 `P => wp(Body, Q)` 형태의 최종 논리식을 만듭니다. (미리 분리해 놓은 VC들이 있다면 그 모든 VC들과 함께)
- `trans_fmla`를 통해 생성된 최종 Z3 논리식 리스트를 `Smt.Solver.check_validity`에 넘깁니다.
- 결과가 `Smt.Solver.VAL` (Valid) 이면 참을, 아니면 거짓을 반환하도록 합니다.

**Step 5. 메인 함수(`verify`) 완성**
- 현재 `verifier.ml`에 작성된 `verify` 함수를 수정하여, 프로그램 내의 각 메서드(`mthd`)에 대해 `Step 4`를 순회하며 실행하도록 엮어줍니다.
- 하나라도 검증에 실패하면 즉시 `false`를 리턴하거나 적절한 오류를 출력하고, 모두 성공하면 `true`를 반환하도록 작성합니다.

## Open Questions

1. **루프 불변식(Loop Invariants)**: 과제에서 요구하는 `while`문의 검증 조건 공식이 정확히 무엇인지, 교재나 강의 자료에 명시된 형태가 있으신가요? (예: WP 계산 중에 사이드 이펙트로 VC 리스트를 별도로 누적할 것인지, 아니면 WP 식 자체에 Forall 한정자를 써서 한 번에 묶을 것인지 등)
2. **배열(Array) 처리 규칙**: `S_assign`에서 배열 업데이트 연산(`E_arr_update`) 처리가 필요한데, Z3의 Array Theory(`Smt.Expr.update_arr`)를 사용하도록 요구받았는지 확인이 필요합니다.
3. 변수 타입 환경(Type Environment) 구성을 위해 함수 매개변수나 로컬 변수의 타입을 어떻게 넘겨줄지에 대한 고려가 되어 있으신가요?

## Verification Plan

### Automated Tests
- 구현이 완료된 후 사용자가 직접 터미널에서 `dune exec -- ./main.exe --input benchmarks/all.dfy` 를 실행하여 검증기의 통과 여부를 확인하도록 안내할 예정입니다.
