use crate::{
    ast::{pool::TermPool, Operator, ParamOperator, Rc, Sort, Term},
    checker::rules::assert_clause_len,
};


use crate::{
    ast::*
};

use super::{assert_eq, RuleArgs, RuleResult};

fn build_term_vec(term: &Rc<Term>, size: usize, pool: &mut dyn TermPool) -> Vec<Rc<Term>> {
    let term = if let Some((Operator::BvBbTerm, args_x)) = term.as_op() {
        args_x.to_vec()
    } else {
        (0..size)
            .map(|i| {
                let op_args = vec![pool.add(Term::new_int(i))];
                pool.add(Term::ParamOp {
                    op: ParamOperator::BvBitOf,
                    op_args,
                    args: vec![term.clone()],
                })
            })
            .collect()
    };
    term
}

pub fn ult(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvult x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let mut expected_res = build_term!(pool, (and (not {x[0].clone()}) {y[0].clone()}));

    for i in 1..size {
        let new_res = build_term!(
            pool,
            (or (and (= {x[i].clone()} {y[i].clone()}) {expected_res.clone()})
                (and (not {x[i].clone()}) {y[i].clone()}))
        );
        expected_res = new_res;
    }

    assert_eq(&expected_res, res)
}

pub fn add(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvadd x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let mut carries = vec![pool.bool_false()];

    for i in 1..size {
        let carry_i = build_term!(
          pool,
          (or (and {x[i - 1].clone()} {y[i - 1].clone()}) (and (xor {x[i - 1].clone()} {y[i - 1].clone()}) {carries[i - 1].clone()}))
        );
        carries.push(carry_i);
    }

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (xor (xor {x[i].clone()} {y[i].clone()}) {carries[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn extract(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (((_, left_j), left_x), right) =
        match_term_err!((= ((_ extract i j) x) (bbterm ...)) = &conclusion[0])?;

    let left_j = left_j.as_integer().unwrap();
    let mut index = left_j;

    if let Some((Operator::BvBbTerm, args)) = left_x.as_op() {
        let mut index = index.to_usize().unwrap();
        for arg in right {
            assert_eq(&args[index], arg)?;
            index += 1;
        }
        return Ok(());
    }

    for arg in right {
        let expected_arg = Term::ParamOp {
            op: ParamOperator::BvBitOf,
            op_args: vec![pool.add(Term::new_int(index.clone()))],
            args: vec![left_x.clone()],
        };
        let new_arg = pool.add(expected_arg);
        assert_eq(&new_arg, arg)?;
        index += 1;
    }
    Ok(())
}

pub fn intblast(RuleArgs { conclusion, pool, ..}: RuleArgs) -> RuleResult {
  assert_clause_len(conclusion, 1)?;
  let (bv_term, int_term) = match_term_err!((= bv_term int_term) = &conclusion[0])?;
  println!("bv_term: {:?}", bv_term);
  println!("int_term: {:?}", int_term);
  let expected_int_term = compute_expected_int_term(bv_term, pool);
  assert_eq(int_term, &expected_int_term)
}


fn get_size(x: &Rc<Term>, pool: &mut dyn TermPool) -> u32 {
  let Sort::BitVec(x_size) = pool.sort(x).as_sort().cloned().unwrap() else {
      unreachable!();
  };
  let x_isize = x_size.to_u32().unwrap();
  x_isize
}

fn uts(x: &Rc<Term>, bv_size: u32,  pool: &mut dyn TermPool) -> Rc<Term> {
  let two : u32 = 2;
  let bv_size_m_1 = bv_size - 1;
  let int_pow_m_1 = two.pow(bv_size_m_1);
  let int_pow = two.pow(bv_size);
  let sign_min = pool.add(Term::new_int(int_pow_m_1));
  let pow2 = pool.add(Term::new_int(int_pow));
  let zero = pool.add(Term::new_int(0));
  let msb_one = build_term!(pool, (< {x.clone()} {sign_min.clone()}));
  let ite = build_term!(pool, (ite {msb_one} {zero} {pow2}));
  build_term!(pool, (- {x.clone()} {ite.clone()}))
}



fn compute_expected_int_term(bv_term : &Rc<Term>, pool: &mut dyn TermPool) -> Rc<Term> {
  let two : u32 = 2;
  match bv_term.as_ref() {
    Term::Op(op, args) => match op {
      Operator::Equals => {
        build_term!(pool, (= {compute_expected_int_term(&args[0], pool)} {compute_expected_int_term(&args[1], pool)}))
      }, 
      Operator::BvAdd => {
        let size = get_size(&args[0], pool);  
        let int_pow = two.pow(size);
        let pow_term = pool.add(Term::new_int(int_pow));
        let addition = build_term!(pool, (+ {compute_expected_int_term(&args[0], pool)} {compute_expected_int_term(&args[1], pool)}));
        let modulus = build_term!(pool, (mod {addition} {pow_term}));
        modulus
      },
      Operator::BvLShr => {
        let size = get_size(&args[0], pool);  
        let zero = pool.add(Term::new_int(0));
        let mut ite = zero;
        let mut body;
        let x = compute_expected_int_term(&args[0], pool);
        let y = compute_expected_int_term(&args[1], pool);
        for i in 0..size {
          let i_term = pool.add(Term::new_int(i));
          let int_pow = two.pow(i);
          let pow_term = pool.add(Term::new_int(int_pow));
          body = build_term!(pool, (div {x.clone()} {pow_term}));
          let eq = build_term!(pool, (= {y.clone()} {i_term}));
          ite = build_term!(pool, (ite {eq} {body} {ite}));
        }
        ite
      },
      Operator::BvSLt => {
        let size = get_size(&args[0], pool);  
        let targ0 = compute_expected_int_term(&args[0], pool);
        let targ1 = compute_expected_int_term(&args[1], pool);
        let uts0 = uts(&targ0, size, pool);
        let uts1 = uts(&targ1, size, pool);
        build_term!(pool, (< {uts0} {uts1}))
      }
      Operator::Not => {
        let trans = compute_expected_int_term(&args[0], pool);
        build_term!(pool, (not {trans}))
      }
      _ => {
        panic!("Unhandled int-blasting op: {}", op);
      },
    },
    Term::Const(Constant::BitVec(value, _)) => {
      pool.add(Term::new_int(value))
    },
    Term::Var(_, _) => {
      build_term!(pool, (ubv_to_int {bv_term.clone()}))
    },
    _ => bv_term.clone()
  }


}

pub fn intblast_bounds(RuleArgs { conclusion,  ..}: RuleArgs) -> RuleResult {
  assert_clause_len(conclusion, 2)
}

