
#[derive(Clone)]
pub enum Ty<A> {
    Lint,
    Fint(u32),
    Constant(i128),
    Lbits,
    Sbits(u32),
    Fbits(u32),
    Unit,
    Bool,
    Bit,
    String,
    Real,
    Enum(A),
    Struct(A),
    Union(A),
    Vector(Box<Ty<A>>),
    List(Box<Ty<A>>),
    Ref(Box<Ty<A>>),
}

#[derive(Clone)]
pub enum Loc<A> {
    Id(A),
    Field(Box<Loc<A>>, A),
    Addr(Box<Loc<A>>),
}

#[derive(Clone, Copy)]
pub enum Op {
    Not,
    Or,
    And,
    Eq,
    Neq,
}

#[derive(Clone)]
pub enum Exp<A> {
    Id(A),
    Ref(A),
    Struct(A, Vec<(A, Exp<A>)>),
    Kind(A, Box<Exp<A>>),
    Unwrap(A, Box<Exp<A>>),
    Field(Box<Exp<A>>, A),
    Call(Op, Vec<Exp<A>>),
}

#[derive(Clone)]
pub enum Instr<A> {
    Decl(A, Ty<A>),
    Init(A, Ty<A>, Exp<A>),
    Clear(A),
    Jump(Exp<A>, usize),
    Goto(usize),
    Copy(Loc<A>, Exp<A>),
    Call(Loc<A>, bool, A, Vec<Exp<A>>),
    Failure,
    Arbitrary,
    End,
}

#[derive(Clone)]
pub enum Def<A> {
    Register(A, Ty<A>),
    Let(Vec<(A, Ty<A>)>, Vec<Instr<A>>),
    Enum(A, Vec<A>),
    Struct(A, Vec<(A, Ty<A>)>),
    Union(A, Vec<(A, Ty<A>)>),
    Val(A, Vec<Ty<A>>, Ty<A>),
    Fn(A, Vec<A>, Vec<Instr<A>>),
}

