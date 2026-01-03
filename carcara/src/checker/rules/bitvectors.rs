use crate::{
    ast::{pool::TermPool, Operator, ParamOperator, Rc, Sort, Term},
    checker::rules::assert_clause_len,
};


use rug::Complete;

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

pub fn binarize(bv_term : &Rc<Term>, pool: &mut dyn TermPool) -> Rc<Term> {
  match bv_term.as_ref() {
    Term::Op(op, args) => match op {
      Operator::BvAdd | Operator::BvMul | Operator::BvAnd | Operator::BvOr | Operator::BvXor | Operator::BvConcat => {
        println!("inside binarize, bv_term:           {:?}", bv_term);
        let n = args.len();
        if n == 1 {
            unreachable!();
        } else if n == 2 {
          let bini0 = binarize(&args[0], pool);
          let bini1 = binarize(&args[1], pool);
          let res = pool.add(Term::Op(*op, vec![bini0, bini1]));
          res
        } else {
          let mut res = args[0].clone();
          for i in 1..n {
            let bini = binarize(&args[i], pool);
            res = pool.add(Term::Op(*op, vec![res, bini]))
          }
          println!("inside binarize, res:           {:?}", &res);
          res
        }
      },
      _ =>  {
          let n = args.len();
          let mut new_vec = Vec::new();
          for i in 0..n {
            let bini = binarize(&args[i], pool);
            new_vec.push(bini);
          }
          let res = pool.add(Term::Op(*op, new_vec));
          res
      }
    }
    _ => bv_term.clone()
  }
}

pub fn intblast(RuleArgs { conclusion, pool, ..}: RuleArgs) -> RuleResult {
  assert_clause_len(conclusion, 1)?;
  let (bv_term, int_term) = match_term_err!((= bv_term int_term) = &conclusion[0])?;
  let binary = binarize(bv_term, pool);
  let expected_int_term = compute_expected_int_term(&binary, pool);
  println!("bv_term:           {:?}", bv_term);
  println!("binary:           {:?}", binary);
  println!("int_term:          {:?}", int_term);
  println!("expected_int_term: {:?}", expected_int_term);
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
  let two = rug::Integer::from(2);
  let bv_size_m_1 = bv_size - 1;
  let int_pow_m_1 = rug::ops::Pow::pow(&two, bv_size_m_1).complete();
  let int_pow = rug::ops::Pow::pow(&two, bv_size).complete();
  let sign_min = pool.add(Term::new_int(int_pow_m_1));
  let pow2 = pool.add(Term::new_int(int_pow));
  let zero = pool.add(Term::new_int(0));
  let msb_one = build_term!(pool, (< {x.clone()} {sign_min.clone()}));
  let ite = build_term!(pool, (ite {msb_one} {zero} {pow2}));
  build_term!(pool, (- {x.clone()} {ite.clone()}))
}

fn bvand(x: &Rc<Term>, y: &Rc<Term>, pool: &mut dyn TermPool) -> Rc<Term> {
        let zero_int = rug::Integer::from(0);
        let zero = pool.add(Term::new_int(zero_int));
        let one_int = rug::Integer::from(1);
        let one = pool.add(Term::new_int(one_int));
        let two = rug::Integer::from(2);
        let two_term = pool.add(Term::new_int(&two));
        let mut sum = zero.clone();
        let targ0 = compute_expected_int_term(x, pool);
        let targ1 = compute_expected_int_term(y, pool);
        let size = get_size(y, pool);  
        for i in 0..size {
            
          let pow_int = rug::ops::Pow::pow(&two, i).complete();
          let pow = pool.add(Term::new_int(pow_int));
          let div1 = build_term!(pool, (div {targ0.clone()} {pow.clone()}));
          let div2 = build_term!(pool, (div {targ1.clone()} {pow.clone()}));
          let extract1 = build_term!(pool, (mod {div1} {two_term.clone()}));
          let extract2 = build_term!(pool, (mod {div2} {two_term.clone()}));
          let eq1 = build_term!(pool, (= {extract1} {one.clone()} ));
          let eq2 = build_term!(pool, (= {extract2} {one.clone()} ));
          let cond = build_term!(pool, (and {eq1} {eq2}));

          let then_branch = one.clone();
          let else_branch = zero.clone();

          let part = build_term!(pool, (ite {cond} {then_branch} {else_branch}));
          let mul = build_term!(pool, (* {pow} {part}));
          sum = build_term!(pool, (+ {sum} {mul}));
        }
        sum
}

fn bvlshr(x: &Rc<Term>, y: &Rc<Term>, pool: &mut dyn TermPool) -> Rc<Term> {
        let two : u32 = 2;
        let size = get_size(x, pool);  
        let zero = pool.add(Term::new_int(0));
        let mut ite = zero;
        let mut body;
        let x = compute_expected_int_term(x, pool);
        let y = compute_expected_int_term(y, pool);
        for i in 0..size {
          let i_term = pool.add(Term::new_int(i));
          let int_pow = two.pow(i);
          let pow_term = pool.add(Term::new_int(int_pow));
          body = build_term!(pool, (div {x.clone()} {pow_term}));
          let eq = build_term!(pool, (= {y.clone()} {i_term}));
          ite = build_term!(pool, (ite {eq} {body} {ite}));
        }
        ite
}


fn bvadd(x: &Rc<Term>, y: &Rc<Term>, pool: &mut dyn TermPool) -> Rc<Term> {
        let two = rug::Integer::from(2);
        let size = get_size(&x, pool);  
        let bigpow = rug::ops::Pow::pow(&two, size);
        let pow_term = pool.add(Term::new_int(bigpow));
        let addition = build_term!(pool, (+ {compute_expected_int_term(&x, pool)} {compute_expected_int_term(&y, pool)}));
        let modulus = build_term!(pool, (mod {addition} {pow_term}));
        modulus
}

fn compute_expected_int_term(bv_term : &Rc<Term>, pool: &mut dyn TermPool) -> Rc<Term> {
  let two = rug::Integer::from(2);
  match bv_term.as_ref() {
    Term::Op(op, args) => match op {
      Operator::Equals => {
        build_term!(pool, (= {compute_expected_int_term(&args[0], pool)} {compute_expected_int_term(&args[1], pool)}))
      }, 
      Operator::BvAdd => {
        let res = bvadd(&args[0], &args[1], pool);
        res
      },
      Operator::BvMul => {
        let size = get_size(&args[0], pool);  
        let bigpow = rug::ops::Pow::pow(&two, size);
        let pow_term = pool.add(Term::new_int(bigpow));
        let mul = build_term!(pool, (* {compute_expected_int_term(&args[0], pool)} {compute_expected_int_term(&args[1], pool)}));
        let modulus = build_term!(pool, (mod {mul} {pow_term}));
        modulus
      },
      Operator::BvUDiv => {
        let two = rug::Integer::from(2);
        let bw : u32 = get_size(&args[0], pool);
        let pow2: rug::Integer = rug::ops::Pow::pow(&two, bw).complete();
        let pow2m1 = pow2 - 1;

        let zero = pool.add(Term::new_int(0));
        let trans0 = compute_expected_int_term(&args[0], pool);
        let trans1 = compute_expected_int_term(&args[1], pool);
        
        let div = build_term!(pool, (div {trans0.clone()} {trans1.clone()}));
        let maxu = pool.add(Term::new_int(pow2m1));
        let cond = build_term!(pool, (= {trans1} {zero}));
        let ite = build_term!(pool, (ite {cond} {maxu} {div}));
        ite
      }
      Operator::BvLShr => {
        let bvlshr_trans = bvlshr(&args[0], &args[1], pool);
        bvlshr_trans
      },
      Operator::BvAShr => {
        let size = get_size(&args[0], pool);  
        let x = compute_expected_int_term(&args[0], pool);
        let bigpow = rug::ops::Pow::pow(&two, size-1);
        let mins = pool.add(Term::new_int(bigpow));
        let lt = build_term!(pool, (< {x.clone()} {mins}));
        let bvnotx = build_term!(pool, (bvnot {args[0].clone()}));
        let lshr1 = bvlshr(&args[0], &args[1], pool);
        let lshr2 = bvlshr(&bvnotx, &args[1], pool);
        let pow2 = rug::ops::Pow::pow(&two, size).complete();
        let pow2m1 = pow2 - 1;
        let pow2m1_term = pool.add(Term::new_int(pow2m1));
        let bvnot = build_term!(pool, (- { pow2m1_term} {lshr2}));
        let ashr = build_term!(pool, (ite {lt} {lshr1.clone()} {bvnot}));
        ashr
      },
      Operator::BvNot => {
        let size = get_size(&args[0], pool);  
        let pow2 = rug::ops::Pow::pow(&two, size).complete();
        let pow2m1 = pow2 - 1;
        let pow2m1_term = pool.add(Term::new_int(pow2m1));
        let trans0 = compute_expected_int_term(&args[0], pool);
        let minus = build_term!(pool, (- {pow2m1_term} {trans0}));
        minus
      }
      Operator::BvNeg => {
        let one_int = rug::Integer::from(1);
        let one = pool.add(Term::new_int(one_int));
        let size = get_size(&args[0], pool);  
        let pow2 = rug::ops::Pow::pow(&two, size).complete();
        let pow2_term = pool.add(Term::new_int(&pow2));
        let pow2m1 = &pow2 - 1;
        let pow2m1_term = pool.add(Term::new_int(pow2m1));
        let trans0 = compute_expected_int_term(&args[0], pool);
        let minus = build_term!(pool, (- {pow2m1_term} {trans0}));
        let plus = build_term!(pool, (+ {minus} {one.clone()}));
        let modu = build_term!(pool, (mod {plus} {pow2_term}));
        modu
      }
      Operator::BvSLt => {
        let size = get_size(&args[0], pool);  
        let targ0 = compute_expected_int_term(&args[0], pool);
        let targ1 = compute_expected_int_term(&args[1], pool);
        let uts0 = uts(&targ0, size, pool);
        let uts1 = uts(&targ1, size, pool);
        build_term!(pool, (< {uts0} {uts1}))
      }
      Operator::BvULt => {
        let targ0 = compute_expected_int_term(&args[0], pool);
        let targ1 = compute_expected_int_term(&args[1], pool);
        build_term!(pool, (< {targ0} {targ1}))
      }
      Operator::BvConcat => {
         println!("concat args[0]:           {:?}", args[0]);
         println!("concat args[1]:           {:?}", args[1]);
        let targ0 = compute_expected_int_term(&args[0], pool);
        let targ1 = compute_expected_int_term(&args[1], pool);
        let size = get_size(&args[1], pool);  
        let pow_int = rug::ops::Pow::pow(&two, size).complete();
        let pow = pool.add(Term::new_int(pow_int));
        let mul = build_term!(pool, (* {targ0} {pow}));
        let plus = build_term!(pool, (+ {mul} {targ1}));
        plus
      }
      Operator::BvAnd => {
        let res = bvand(&args[0], &args[1], pool);
        res
      }
      Operator::BvOr => {
        let size = get_size(&args[1], pool);  
        let pow_int = rug::ops::Pow::pow(&two, size).complete();
        let pow = pool.add(Term::new_int(pow_int));
        let bvadd1 = bvadd(&args[0], &args[1], pool);
        let bvand1 = bvand(&args[0], &args[1], pool);
        let sub = build_term!(pool, (- {bvadd1} {bvand1}));
        let modulus = build_term!(pool, (mod {sub} {pow}));
        modulus
      }
      Operator::Not => {
        let trans = compute_expected_int_term(&args[0], pool);
        build_term!(pool, (not {trans}))
      }
      Operator::And => {
        let mut new_args: Vec<Rc<Term>> = Vec::new();
        for arg in args {
          let trans_arg = compute_expected_int_term(arg, pool);
          new_args.push(trans_arg.clone());
        }
        pool.add(Term::Op(Operator::And, new_args))
      }
      Operator::Or => {
        let mut new_args: Vec<Rc<Term>> = Vec::new();
        for arg in args {
          let trans_arg = compute_expected_int_term(arg, pool);
          new_args.push(trans_arg.clone());
        }
        pool.add(Term::Op(Operator::Or, new_args))
      }
      Operator::Implies => {
        let trans0 = compute_expected_int_term(&args[0], pool);
        let trans1 = compute_expected_int_term(&args[1], pool);
        build_term!(pool, (=> {trans0} {trans1}))
      }
      Operator::Ite => {
        let trans0 = compute_expected_int_term(&args[0], pool);
        let trans1 = compute_expected_int_term(&args[1], pool);
        let trans2 = compute_expected_int_term(&args[2], pool);
        build_term!(pool, (ite {trans0} {trans1} {trans2}))
      }
      Operator::UBvToInt => {
        let trans = compute_expected_int_term(&args[0], pool);
        trans.clone()
      }
      Operator::GreaterEq => {
        let trans0 = compute_expected_int_term(&args[0], pool);
        let trans1 = compute_expected_int_term(&args[1], pool);
        build_term!(pool, (>= {trans0} {trans1}))
      }
      Operator::Add => {
        let trans0 = compute_expected_int_term(&args[0], pool);
        let trans1 = compute_expected_int_term(&args[1], pool);
        build_term!(pool, (+ {trans0} {trans1}))
      }
      Operator::Mult => {
        let trans0 = compute_expected_int_term(&args[0], pool);
        let trans1 = compute_expected_int_term(&args[1], pool);
        build_term!(pool, (* {trans0} {trans1}))
      }
      _ => {
        panic!("Unhandled int-blasting op: {}", op);
      },
    },
    Term::ParamOp {op, op_args, args} => match op {
      ParamOperator::BvExtract => {
        let high_opt = op_args[0].as_integer();
        let low_opt = op_args[1].as_integer();
        let high: u32 = high_opt
           .and_then(|x| x.to_u32())      // Option<Integer> -> Option<i32>
           .expect("no high or doesn't fit");
        let low: u32 = low_opt
           .and_then(|x| x.to_u32())      // Option<Integer> -> Option<i32>
           .expect("no high or doesn't fit");
        let sub = high - low + 1;
        let trans0 = compute_expected_int_term(&args[0], pool);
        let int_pow2_low = rug::ops::Pow::pow(&two, low).complete();
        let int_pow2_sub = rug::ops::Pow::pow(&two, sub).complete();
        let pow2_low = pool.add(Term::new_int(int_pow2_low));
        let pow2_sub = pool.add(Term::new_int(int_pow2_sub));
        let div = build_term!(pool, (div {trans0} {pow2_low}));
        let modulus = build_term!(pool, (mod {div} {pow2_sub}));
        modulus
      }
      _ => {
        panic!("Unhandled int-blasting op: {}", op);
      }
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

pub fn intblast_bounds(RuleArgs { conclusion, pool,  ..}: RuleArgs) -> RuleResult {
  let two = rug::Integer::from(2);
  let (lower, upper) = match_term_err!((and lower upper) = &conclusion[0])?;
  let (t0, b0) = match_term_err!((>= t b) = lower)?; 
  let (t1, b1) = match_term_err!((not (>= t b)) = upper)?; 
  let bv_var_0 = match_term_err!((ubv_to_int bv_var) = t0)?;
  let bv_var_1 = match_term_err!((ubv_to_int bv_var) = t1)?;
  assert_eq(bv_var_0, bv_var_1)?;
  let bw = get_size(&bv_var_0, pool);
  let zero_term = pool.add(Term::new_int(0));
  let bigpow = rug::ops::Pow::pow(&two, bw);
  let pow_term = pool.add(Term::new_int(bigpow));
  match b0.as_ref() {
      Term::Const(Constant::Integer(_)) => {
        match b1.as_ref() {
          Term::Const(Constant::Integer(_)) => {
            assert_eq(b0, &zero_term)?;
            assert_eq(b1, &pow_term)?;
          }
          _ => {
          }
        }
    }
    _ => {
    }

  }
  // match conclusion.as_ref() {
  //   Term::Op(op, args) => match op {
  //     Operator::UbvToInt => {
  //       let size = get_size(&args[0], pool);
  //     }
  //   }
  // }
  assert_eq(lower, lower)
}

