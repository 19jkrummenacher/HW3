// By Jonathan Krummenacher Final Project
// references https://dafny.org/dafny/DafnyRef/DafnyRef  https://www.lexicalscope.com/blog/2016/02/13/dafny-matrix-mutiplication/ 
module vectors
{

    trait Operators<T>
    {
        function method zero(): T // this is the 0 of the element this is required to check for division of zero.
        function method plus(l: T, r: T) : T // adding two elements
        function method sub(l: T, r: T) : T // subbing two elements
        function  method multi(l: T, r: T) : T // multipling two elements
        function  method div(l: T, r: T) : T 
            requires r != zero() // dividing two elements
        function method neg(l: T) : T // negating an element.
        function method equals(l: T, r: T): bool
        function method notEquals(l: T, r: T): bool
    }
    class RealOp extends Operators<real>
    {
        constructor() {}
        function method zero(): real {0.0}
        function method plus(l: real, r: real) : real {l + r} // adding two elements
        function method sub(l: real, r: real) : real {l - r}// subbing two elements
        function  method multi(l: real, r: real) : real {l * r}// multipling two elements
        function  method div(l: real, r: real) : real requires r != 0.0 {l / r} // dividing two elements
        function method neg(l: real) : real {-1.0 * l}
        function method equals(l: real, r: real): bool {l + 0.00001 > r && l - 0.00001 < r} // no real reason I chose 0.00001 but I did want to accound for float weirdness
        function method notEquals(l: real, r: real): bool {l + 0.00001 < r && l - 0.00001 > r}
    }

    class IntOp extends Operators<int>
    {
        constructor() {}
        function method zero(): int {0}
        function method plus(l: int, r: int) : int {l + r} // adding two elements
        function method sub(l: int, r: int) : int {l - r}// subbing two elements
        function  method multi(l: int, r: int) : int {l * r}// multipling two elements
        function  method div(l: int, r: int) : int requires r != 0 {l / r} // dividing two elements
        function method neg(l: int) : int {-1 * l}
        function method equals(l: int, r: int): bool {l == r}
        function method notEquals(l: int, r: int): bool {l != r}
    }

    class Vec2 <T>
    {
        var v1 : T
        var v2 : T
        const op: Operators<T>

        predicate Valid() 
        {
            true
        }

        constructor (v1 : T, v2 : T, op: Operators<T>)
            ensures this.v1 == v1 && this.v2 == v2
        {
            this.v1 := v1;
            this.v2 := v2;
            this.op := op;
        }


        // cyVector.h::228 unary minus -1 * vec2
        function method unaryNegation(): (T, T)
        reads this
        {
            (op.neg(this.v1),op.neg(this.v2))
        }

        // cyVector.h::231
        function method BinaryAdd(other: Vec2<T>): (T, T)
        reads this, other, this.op, other.op
        {
            (op.plus(this.v1, other.v1), op.plus(this.v2, other.v2))
        }
        // cyVector.h::235 constant
        function method BinaryAddC(other: T): (T, T)
        reads this
        {
            (op.plus(this.v1, other), op.plus(this.v2, other))
        }
        // cyVector.h::232
        function method BinarySub(other: Vec2<T>): (T, T)
        reads this, other
        {
            (op.sub(this.v1, other.v1), op.sub(this.v2, other.v2))
        }
        // cyVector.h::236 constant
        function method BinarySubC(other: T): (T, T)
        reads this
        {
            (op.sub(this.v1, other), op.sub(this.v2, other))
        }
        // cyVector.h::233
        function method BinaryMulti(other: Vec2<T>): (T, T)
        reads this, other
        {
            (op.multi(this.v1, other.v1), op.multi(this.v2, other.v2))
        }
        // cyVector.h::237 constant
        function method BinaryMultiC(other: T): (T, T)
        reads this
        {
            (op.multi(this.v1, other), op.multi(this.v2, other))
        }
        // cyVector.h::234
        function method BinaryDiv(other: Vec2<T>): (T, T)
        reads this, other
        requires other.v1 != op.zero() && other.v2 != op.zero()
        {
            (op.div(this.v1, other.v1), op.div(this.v2, other.v2))
        }
        // cyVector.h::238 constant
        function method BinaryDivC(other: T): (T, T)
        reads this
        requires other != op.zero()
        {
            (op.div(this.v1, other), op.div(this.v2, other))
        }

        // assignment Add cyVector.h:241
        method AssignmentAdd(other: Vec2<T>)
        requires this.op == other.op && this.Valid() && other.Valid()
        modifies this
        ensures (v1, v2) == old(BinaryAdd(other))
        {
            var (a1, a2) := BinaryAdd(other);
            this.v1 := a1;
            this.v2 := a2;
        }

        // assignment Add cyVector.h:245 constant
        method AssignmentAddC(other: T)
        requires this.Valid()
        modifies this
        ensures (v1, v2) == old(BinaryAddC(other))
        {
            var (a1, a2) := BinaryAddC(other);
            this.v1 := a1;
            this.v2 := a2;
        }


        // cyVector.h:242 Assignment Subtract
        method AssignmentSub(other: Vec2<T>)
        requires this.op == other.op && this.Valid() && other.Valid()
        modifies this
        ensures (v1, v2) == old(BinarySub(other))
        {
            var (s1, s2) := BinarySub(other);
            this.v1 := s1;
            this.v2 := s2;
        }

        // cyVector.h:246 Assignment Subtract constant
        method AssignmentSubC(other: T)
        requires this.Valid()
        modifies this
        ensures (v1, v2) == old(BinarySubC(other))
        {
            var (s1, s2) := BinarySubC(other);
            this.v1 := s1;
            this.v2 := s2;
        }

        // cyVector.h:243 Assignment Multiply constant
        method AssignmentMulti(other: Vec2<T>)
        requires this.op == other.op && this.Valid() && other.Valid()
        modifies this
        ensures (v1, v2) == old(BinaryMulti(other))
        {
            var (m1, m2) := BinaryMulti(other);
            this.v1 := m1;
            this.v2 := m2;
        }

        // cyVector.h:247 Assignment Multiply constant
        method AssignmentMultiC(other: T)
        requires this.Valid()
        modifies this
        ensures (v1, v2) == old(BinaryMultiC(other))
        {
            var (m1, m2) := BinaryMultiC(other);
            this.v1 := m1;
            this.v2 := m2;
        }

        // cyVector.h:244 Assignment Divide
        method AssignmentDiv(other: Vec2<T>)
        requires this.op == other.op && this.Valid() && other.Valid() && other.v1 != op.zero() && other.v2 != op.zero()
        modifies this
        ensures (v1, v2) == old(BinaryDiv(other))
        {
            var (d1, d2) := BinaryDiv(other);
            this.v1 := d1;
            this.v2 := d2;
        }

        // cyVector.h:248 Assignment Divide constant
        method AssignmentDivC(other: T)
        requires this.Valid() && other != op.zero()
        modifies this
        ensures (v1, v2) == old(BinaryDivC(other))
        {
            var (d1, d2) := BinaryDivC(other);
            this.v1 := d1;
            this.v2 := d2;
        }

        // cyVector.h:263 
        function Dot(other: Vec2<T>): T
        reads this, other, this.op
        {
            op.plus(op.multi(this.v1, other.v1), op.multi(this.v2, other.v2))
        }
        // cyVector.h:265
        function Cross(other: Vec2<T>): T
        reads this, other, this.op

        {
            op.plus(op.multi(op.neg(this.v2), other.v1), op.multi(this.v1, other.v2))
        }



    }


    class Vec3 <T>
    {
        var v1 : T
        var v2 : T
        var v3 : T
        const op: Operators<T>

        predicate Valid() 
        {
            true
        }

        constructor (v1 : T, v2 : T, v3 : T, op: Operators<T>)
            ensures this.v1 == v1 && this.v2 == v2 && this.v3 == v3
        {
            this.v1 := v1;
            this.v2 := v2;
            this.v3 := v3;
            this.op := op;
        }

        // cyVector.h::228 unary minus -1 * Vec3
        function method unaryNegation(): (T, T, T)
        reads this
        {
            (op.neg(this.v1),op.neg(this.v2), op.neg(this.v3))
        }

        // cyVector.h::231
        function method BinaryAdd(other: Vec3<T>): (T, T, T)
        reads this, other, this.op, other.op
        {
            (op.plus(this.v1, other.v1), op.plus(this.v2, other.v2), op.plus(this.v3, other.v3))
        }
        // cyVector.h::235 constant
        function method BinaryAddC(other: T): (T, T, T)
        reads this
        {
            (op.plus(this.v1, other), op.plus(this.v2, other), op.plus(this.v3, other))
        }
        // cyVector.h::232
        function method BinarySub(other: Vec3<T>): (T, T, T)
        reads this, other
        {
            (op.sub(this.v1, other.v1), op.sub(this.v2, other.v2), op.sub(this.v3, other.v3))
        }
        // cyVector.h::236 constant
        function method BinarySubC(other: T): (T, T, T)
        reads this
        {
            (op.sub(this.v1, other), op.sub(this.v2, other), op.sub(this.v3, other))
        }
        // cyVector.h::233
        function method BinaryMulti(other: Vec3<T>): (T, T, T)
        reads this, other
        {
            (op.multi(this.v1, other.v1), op.multi(this.v2, other.v2), op.multi(this.v3, other.v3))
        }
        // cyVector.h::237 constant
        function method BinaryMultiC(other: T): (T, T, T)
        reads this
        {
            (op.multi(this.v1, other), op.multi(this.v2, other), op.multi(this.v3, other))
        }
        // cyVector.h::234
        function method BinaryDiv(other: Vec3<T>): (T, T, T)
        reads this, other
        requires other.v1 != op.zero() && other.v2 != op.zero() && other.v3 != op.zero()
        {
            (op.div(this.v1, other.v1), op.div(this.v2, other.v2), op.div(this.v3, other.v3))
        }
        // cyVector.h::238 constant
        function method BinaryDivC(other: T): (T, T, T)
        reads this
        requires other != op.zero()
        {
            (op.div(this.v1, other), op.div(this.v2, other), op.div(this.v3, other))
        }

        // assignment Add cyVector.h:241
        method AssignmentAdd(other: Vec3<T>)
        requires this.op == other.op && this.Valid() && other.Valid()
        modifies this
        ensures (v1, v2, v3) == old(BinaryAdd(other))
        {
            var (a1, a2, a3) := BinaryAdd(other);
            this.v1 := a1;
            this.v2 := a2;
            this.v3 := a3;
        }

        // assignment Add cyVector.h:245 constant
        method AssignmentAddC(other: T)
        requires this.Valid()
        modifies this
        ensures (v1, v2, v3) == old(BinaryAddC(other))
        {
            var (a1, a2, a3) := BinaryAddC(other);
            this.v1 := a1;
            this.v2 := a2;
            this.v3 := a3;
        }


        // cyVector.h:242 Assignment Subtract
        method AssignmentSub(other: Vec3<T>)
        requires this.op == other.op && this.Valid() && other.Valid()
        modifies this
        ensures (v1, v2, v3) == old(BinarySub(other))
        {
            var (s1, s2, s3) := BinarySub(other);
            this.v1 := s1;
            this.v2 := s2;
            this.v3 := s3;
        }

        // cyVector.h:246 Assignment Subtract constant
        method AssignmentSubC(other: T)
        requires this.Valid()
        modifies this
        ensures (v1, v2, v3) == old(BinarySubC(other))
        {
            var (s1, s2, s3) := BinarySubC(other);
            this.v1 := s1;
            this.v2 := s2;
            this.v3 := s3;
        }

        // cyVector.h:243 Assignment Multiply constant
        method AssignmentMulti(other: Vec3<T>)
        requires this.op == other.op && this.Valid() && other.Valid()
        modifies this
        ensures (v1, v2, v3) == old(BinaryMulti(other))
        {
            var (m1, m2, m3) := BinaryMulti(other);
            this.v1 := m1;
            this.v2 := m2;
            this.v3 := m3;
        }

        // cyVector.h:247 Assignment Multiply constant
        method AssignmentMultiC(other: T)
        requires this.Valid()
        modifies this
        ensures (v1, v2, v3) == old(BinaryMultiC(other))
        {
            var (m1, m2, m3) := BinaryMultiC(other);
            this.v1 := m1;
            this.v2 := m2;
            this.v3 := m3;
        }

        // cyVector.h:244 Assignment Divide
        method AssignmentDiv(other: Vec3<T>)
        requires this.op == other.op && this.Valid() && other.Valid() && other.v1 != op.zero() && other.v2 != op.zero() && other.v3 != op.zero()
        modifies this
        ensures (v1, v2, v3) == old(BinaryDiv(other))
        {
            var (d1, d2, d3) := BinaryDiv(other);
            this.v1 := d1;
            this.v2 := d2;
            this.v3 := d3;
        }

        // cyVector.h:248 Assignment Divide constant
        method AssignmentDivC(other: T)
        requires this.Valid() && other != op.zero()
        modifies this
        ensures (v1, v2, v3) == old(BinaryDivC(other))
        {
            var (d1, d2, d3) := BinaryDivC(other);
            this.v1 := d1;
            this.v2 := d2;
            this.v3 := d3;
        }

        // cyVector.h:263 
        function Dot(other: Vec3<T>): T
        reads this, other, this.op
        {
            op.plus(op.plus(op.multi(this.v1, other.v1), op.multi(this.v2, other.v2)), op.multi(this.v2, other.v2)) // the order of operations on the last bit is techinacally disjointed but it shouldn't affect the results.
        }
        // cyVector.h:265
        function Cross(other: Vec3<T>): (T, T, T)
        reads this, other, this.op

        { // Vec3(y*p.z-z*p.y, z*p.x-x*p.z, x*p.y-y*p.x);
            (op.sub(op.multi(this.v2, other.v3),op.multi(op.neg(this.v3), other.v2)),op.sub(op.multi(this.v3, other.v1),op.multi(op.neg(this.v1), other.v3)),op.sub(op.multi(this.v1, other.v2),op.multi(op.neg(this.v2), other.v1)))
        }


    }

    class VecN <T(==)>
    {
        var vn : seq<T>
        const op: Operators<T>
        constructor (vn : seq<T>, op: Operators<T>)
            ensures this.vn == vn
        {
            this.vn := vn;
            this.op := op;
        }

        // cyVector.h::228 unary minus -1 * Vec3
        function method unaryNegation(): seq<T>
        reads this, this.op
        {
            seq(|this.vn|, i requires 0 <= i < |this.vn| reads this => this.op.neg(this.vn[i]))
        }

        // cyVector.h::231
        function method BinaryAdd(other: VecN<T>): seq<T>
        requires this.op == other.op && |this.vn| == |other.vn|
        reads this, other, this.op, other.op
        {
            seq(|this.vn|, i requires 0 <= i < |this.vn| && 0 <= i < |other.vn| reads this, other => op.plus(this.vn[i], other.vn[i]))
        }
        // cyVector.h::235 constant
        function method BinaryAddC(other: T): seq<T>
        reads this
        {
            seq(|this.vn|, i requires 0 <= i < |this.vn| reads this => op.plus(this.vn[i], other))
        }
        // cyVector.h::232
        function method BinarySub(other: VecN<T>): seq<T>
        requires this.op == other.op && |this.vn| == |other.vn|
        reads this, other, this.op, other.op
        {
            seq(|this.vn|, i requires 0 <= i < |this.vn| && 0 <= i < |other.vn| reads this, other => op.sub(this.vn[i], other.vn[i]))
        }
        // cyVector.h::236 constant
        function method BinarySubC(other: T): seq<T>
        reads this
        {
            seq(|this.vn|, i requires 0 <= i < |this.vn| reads this => op.sub(this.vn[i], other))
        }
        // cyVector.h::233
        function method BinaryMulti(other: VecN<T>): seq<T>
        requires this.op == other.op && |this.vn| == |other.vn|
        reads this, other, this.op, other.op
        {
            seq(|this.vn|, i requires 0 <= i < |this.vn| && 0 <= i < |other.vn| reads this, other => this.op.multi(this.vn[i], other.vn[i]))
        }
        // cyVector.h::237 constant
        function method BinaryMultiC(other: T): seq<T>
        reads this
        {
            seq(|this.vn|, i requires 0 <= i < |this.vn| reads this => this.op.multi(this.vn[i], other))
        }
        // cyVector.h::234
        function method BinaryDiv(other: VecN<T>): seq<T>
        requires this.op == other.op && |this.vn| == |other.vn|
        requires forall i | 0 <= i < |other.vn| :: other.vn[i] != op.zero()  // check that the sequence doesn't have a hidden zero
        reads this, other, this.op, other.op
        {
            seq(|this.vn|, i requires 0 <= i < |this.vn| && 0 <= i < |other.vn| && other.vn[i] != this.op.zero() reads this, other => this.op.div(this.vn[i], other.vn[i]))
        }
        // cyVector.h::238 constant
        function method BinaryDivC(other: T): seq<T>
        reads this
        requires other != op.zero()
        {
            seq(|this.vn|, i requires 0 <= i < |this.vn| reads this => op.div(this.vn[i], other))
        }

        // assignment Add cyVector.h:241
        method AssignmentAdd(other: VecN<T>)
        requires this.op == other.op && |this.vn| == |other.vn|
        modifies this
        ensures vn == old(BinaryAdd(other))
        {
            this.vn := BinaryAdd(other);
        }

        // assignment Add cyVector.h:245 constant
        method AssignmentAddC(other: T)
        modifies this
        ensures vn == old(BinaryAddC(other))
        {
            this.vn := BinaryAddC(other);
        }


        // cyVector.h:242 Assignment Subtract
        method AssignmentSub(other: VecN<T>)
        requires this.op == other.op && |this.vn| == |other.vn|
        modifies this
        ensures vn == old(BinarySub(other))
        {
            this.vn := BinarySub(other);
        }

        // cyVector.h:246 Assignment Subtract constant
        method AssignmentSubC(other: T)
        modifies this
        ensures vn == old(BinarySubC(other))
        {
            this.vn := BinarySubC(other);
        }

        // cyVector.h:243 Assignment Multiply constant
        method AssignmentMulti(other: VecN<T>)
        requires this.op == other.op && |this.vn| == |other.vn|
        modifies this
        ensures vn == old(BinaryMulti(other))
        {
            this.vn := BinaryMulti(other);
        }

        // cyVector.h:247 Assignment Multiply constant
        method AssignmentMultiC(other: T)
        modifies this
        ensures vn == old(BinaryMultiC(other))
        {
            this.vn := BinaryMultiC(other);
        }

        // cyVector.h:244 Assignment Divide
        method AssignmentDiv(other: VecN<T>)
        requires this.op == other.op && |this.vn| == |other.vn|
        requires forall i | 0 <= i < |other.vn| :: other.vn[i] != op.zero()
        modifies this
        ensures vn == old(BinaryDiv(other))
        {
            this.vn := BinaryDiv(other);
        }

        // cyVector.h:248 Assignment Divide constant
        method AssignmentDivC(other: T)
        requires other != op.zero()
        modifies this
        ensures vn == old(BinaryDivC(other))
        {
            this.vn := BinaryDivC(other);
        }

        // cyVector.h:263 
        method Dot(other: VecN<T>) returns(sum: T)
        requires this.op == other.op && |this.vn| == |other.vn|
        {
            sum := op.zero();
            var i := 0;
            while i < |other.vn|
                invariant 0 <= i <= |other.vn|
                decreases |other.vn| - i
            {
                sum := op.plus(sum, op.multi(this.vn[i], other.vn[i]));
                i := i+1;
            }           

        }
        // No cross product.
    }

    class Mat2 <T>
    {
        var mx : seq<seq<T>>
        const op: Operators<T>

        predicate Valid() 
        reads this
        {
            |mx| == 2 && |mx[0]| == 2
        }

        constructor (mx: seq<seq<T>>, op: Operators<T>)
        {
            this.mx := mx;
            this.op := op;
        }

        function method unaryNegation(): ((T,T), (T,T))
        requires |mx| == 2 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 2
        reads this, this.op
        {
            ((op.neg(mx[0][0]),op.neg(mx[0][1])), (op.neg(mx[1][0]), op.neg(mx[1][1])))
        }

        function method BinaryAdd(other: Mat2<T>): ((T,T), (T,T))
        requires |mx| == 2 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 2
        requires |other.mx| == 2 && forall i :: 0 <= i < |other.mx| ==> |other.mx[i]| == 2
        reads this, other
        {
            ((op.plus(mx[0][0],other.mx[0][0]),op.plus(mx[0][1],other.mx[0][1])) , (op.plus(mx[1][0],other.mx[1][0]),op.plus(mx[1][1],other.mx[1][1])))
        }

        function method BinarySub(other: Mat2<T>): ((T,T), (T,T))
        requires |mx| == 2 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 2
        requires |other.mx| == 2 && forall i :: 0 <= i < |other.mx| ==> |other.mx[i]| == 2
        reads this, other
        {
            ((op.sub(mx[0][0],other.mx[0][0]),op.sub(mx[0][1],other.mx[0][1])) , (op.sub(mx[1][0],other.mx[1][0]),op.sub(mx[1][1],other.mx[1][1])))
        }

        function method BinaryMulti(other: Mat2<T>): ((T,T), (T,T))
        requires |mx| == 2 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 2
        requires |other.mx| == 2 && forall i :: 0 <= i < |other.mx| ==> |other.mx[i]| == 2
        reads this, other
        {
            (( op.plus(op.multi(mx[0][0],other.mx[0][0]), op.multi(mx[0][1],other.mx[1][0])), op.plus(op.multi(mx[0][0],other.mx[0][1]), op.multi(mx[0][1],other.mx[1][1]))), (op.plus(op.multi(mx[1][0],other.mx[0][0]), op.multi(mx[1][1],other.mx[1][0])),   op.plus(op.multi(mx[1][0],other.mx[0][1]), op.multi(mx[1][1],other.mx[1][1]))))
        }
        
    }

    class Mat3 <T>
    {
        var mx : seq<seq<T>>
        const op: Operators<T>

        predicate Valid() 
        reads this
        {
            |mx| == 3 && |mx[0]| == 3
        }

        constructor (mx: seq<seq<T>>, op: Operators<T>)
        {
            this.mx := mx;
            this.op := op;
        }

        function method unaryNegation(): ((T, T, T), (T, T, T), (T, T, T))
        requires |mx| == 3 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 3
        reads this, this.op
        {
            ((op.neg(mx[0][0]),op.neg(mx[0][1]), op.neg(mx[0][2])), (op.neg(mx[1][0]),op.neg(mx[1][1]), op.neg(mx[1][2])), (op.neg(mx[2][0]),op.neg(mx[2][1]), op.neg(mx[2][2])))
        }

        function method BinaryAdd(other: Mat3<T>): ((T, T, T), (T, T, T), (T, T, T))
        requires |mx| == 3 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 3
        requires |other.mx| == 3 && forall i :: 0 <= i < |other.mx| ==> |other.mx[i]| == 3
        reads this, other
        {
            ((op.plus(mx[0][0],other.mx[0][0]),op.plus(mx[0][1],other.mx[0][1]),op.plus(mx[0][2],other.mx[0][2])),
            (op.plus(mx[1][0],other.mx[1][0]),op.plus(mx[1][1],other.mx[1][1]),op.plus(mx[1][2],other.mx[1][2])),
            (op.plus(mx[2][0],other.mx[2][0]),op.plus(mx[2][1],other.mx[2][1]),op.plus(mx[2][2],other.mx[2][2])))
        }

        function method BinarySub(other: Mat3<T>): ((T, T, T), (T, T, T), (T, T, T))
        requires |mx| == 3 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 3
        requires |other.mx| == 3 && forall i :: 0 <= i < |other.mx| ==> |other.mx[i]| == 3
        reads this, other
        {
            ((op.sub(mx[0][0],other.mx[0][0]),op.sub(mx[0][1],other.mx[0][1]),op.sub(mx[0][2],other.mx[0][2])),
            (op.sub(mx[1][0],other.mx[1][0]),op.sub(mx[1][1],other.mx[1][1]),op.sub(mx[1][2],other.mx[1][2])),
            (op.sub(mx[2][0],other.mx[2][0]),op.sub(mx[2][1],other.mx[2][1]),op.sub(mx[2][2],other.mx[2][2])))
        }

    } 

    class Mat34 <T>
    {
        var mx : seq<seq<T>>
        const op: Operators<T>

        predicate Valid() 
        reads this
        {
            |mx| == 4 && |mx[0]| == 3
        }

        constructor (mx: seq<seq<T>>, op: Operators<T>)
        {
            this.mx := mx;
            this.op := op;
        }

        function method unaryNegation(): ((T, T, T), (T, T, T), (T, T, T), (T, T, T))
        requires |mx| == 4 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 3
        reads this, this.op
        {
            ((op.neg(mx[0][0]),op.neg(mx[0][1]), op.neg(mx[0][2])), (op.neg(mx[1][0]),op.neg(mx[1][1]), op.neg(mx[1][2])), (op.neg(mx[2][0]),op.neg(mx[2][1]), op.neg(mx[2][2])), (op.neg(mx[3][0]),op.neg(mx[3][1]), op.neg(mx[3][2])))
        }

        function method BinaryAdd(other: Mat34<T>): ((T, T, T), (T, T, T), (T, T, T), (T, T, T))
        requires |mx| == 4 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 3
        requires |other.mx| == 4 && forall i :: 0 <= i < |other.mx| ==> |other.mx[i]| == 3
        reads this, other
        {
            ((op.plus(mx[0][0],other.mx[0][0]),op.plus(mx[0][1],other.mx[0][1]),op.plus(mx[0][2],other.mx[0][2])),
            (op.plus(mx[1][0],other.mx[1][0]),op.plus(mx[1][1],other.mx[1][1]),op.plus(mx[1][2],other.mx[1][2])),
            (op.plus(mx[2][0],other.mx[2][0]),op.plus(mx[2][1],other.mx[2][1]),op.plus(mx[2][2],other.mx[2][2])),
            (op.plus(mx[3][0],other.mx[3][0]),op.plus(mx[3][1],other.mx[3][1]),op.plus(mx[3][2],other.mx[3][2])))
        }

        function method BinarySub(other: Mat34<T>): ((T, T, T), (T, T, T), (T, T, T), (T, T, T))
        requires |mx| == 4 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 3
        requires |other.mx| == 4 && forall i :: 0 <= i < |other.mx| ==> |other.mx[i]| == 3
        reads this, other
        {
            ((op.sub(mx[0][0],other.mx[0][0]),op.sub(mx[0][1],other.mx[0][1]),op.sub(mx[0][2],other.mx[0][2])),
            (op.sub(mx[1][0],other.mx[1][0]),op.sub(mx[1][1],other.mx[1][1]),op.sub(mx[1][2],other.mx[1][2])),
            (op.sub(mx[2][0],other.mx[2][0]),op.sub(mx[2][1],other.mx[2][1]),op.sub(mx[2][2],other.mx[2][2])),
            (op.sub(mx[3][0],other.mx[3][0]),op.sub(mx[3][1],other.mx[3][1]),op.sub(mx[3][2],other.mx[3][2])))
        }
    }

    class Mat4 <T>
    {
        var mx : seq<seq<T>>
        const op: Operators<T>

        predicate Valid() 
        reads this
        {
            |mx| == 4 && |mx[0]| == 4
        }

        constructor (mx: seq<seq<T>>, op: Operators<T>)
        {
            this.mx := mx;
            this.op := op;
        }

        function method unaryNegation(): ((T, T, T, T), (T, T, T, T), (T, T, T, T), (T, T, T, T))
        requires |mx| == 4 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 4
        reads this, this.op
        {
            ((op.neg(mx[0][0]),op.neg(mx[0][1]), op.neg(mx[0][2]), op.neg(mx[0][3])), (op.neg(mx[1][0]),op.neg(mx[1][1]), op.neg(mx[1][2]), op.neg(mx[1][3])), (op.neg(mx[2][0]),op.neg(mx[2][1]), op.neg(mx[2][2]), op.neg(mx[2][3])), (op.neg(mx[3][0]),op.neg(mx[3][1]), op.neg(mx[3][2]), op.neg(mx[3][3])))
        }

        function method BinaryAdd(other: Mat4<T>): ((T, T, T, T), (T, T, T, T), (T, T, T, T), (T, T, T, T))
        requires |mx| == 4 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 4
        requires |other.mx| == 4 && forall i :: 0 <= i < |other.mx| ==> |other.mx[i]| == 4
        reads this, other
        {
            ((op.plus(mx[0][0],other.mx[0][0]),op.plus(mx[0][1],other.mx[0][1]),op.plus(mx[0][2],other.mx[0][2]),op.plus(mx[0][3],other.mx[0][3])),
            (op.plus(mx[1][0],other.mx[1][0]),op.plus(mx[1][1],other.mx[1][1]),op.plus(mx[1][2],other.mx[1][2]),op.plus(mx[1][3],other.mx[1][3])),
            (op.plus(mx[2][0],other.mx[2][0]),op.plus(mx[2][1],other.mx[2][1]),op.plus(mx[2][2],other.mx[2][2]),op.plus(mx[2][3],other.mx[2][3])),
            (op.plus(mx[3][0],other.mx[3][0]),op.plus(mx[3][1],other.mx[3][1]),op.plus(mx[3][2],other.mx[3][2]),op.plus(mx[3][3],other.mx[3][3])))
        }

        function method BinarySub(other: Mat4<T>): ((T, T, T, T), (T, T, T, T), (T, T, T, T), (T, T, T, T))
        requires |mx| == 4 && forall i :: 0 <= i < |mx| ==> |mx[i]| == 4
        requires |other.mx| == 4 && forall i :: 0 <= i < |other.mx| ==> |other.mx[i]| == 4
        reads this, other
        {
            ((op.sub(mx[0][0],other.mx[0][0]),op.sub(mx[0][1],other.mx[0][1]),op.sub(mx[0][2],other.mx[0][2]),op.sub(mx[0][3],other.mx[0][3])),
            (op.sub(mx[1][0],other.mx[1][0]),op.sub(mx[1][1],other.mx[1][1]),op.sub(mx[1][2],other.mx[1][2]),op.sub(mx[1][3],other.mx[1][3])),
            (op.sub(mx[2][0],other.mx[2][0]),op.sub(mx[2][1],other.mx[2][1]),op.sub(mx[2][2],other.mx[2][2]),op.sub(mx[2][3],other.mx[2][3])),
            (op.sub(mx[3][0],other.mx[3][0]),op.sub(mx[3][1],other.mx[3][1]),op.sub(mx[3][2],other.mx[3][2]),op.sub(mx[3][3],other.mx[3][3])))
        }
    }



    method Main()
    {
        var intMath:= new IntOp(); // this is for whole number math.
        var realMath := new RealOp(); // Any math that has a fraction or decimal
        // ================================ test vectors ====================================
        // Vec2
        
        var v2int:= new Vec2<int>(0, 0, intMath); // this example uses an int.
        var v2real := new Vec2<real>(0.0, 0.0, realMath);

        // Vec3
        var v3int:= new Vec3<int>(0, 0, 0, intMath);
        var v3real:= new Vec3<real>(0.0, 0.0, 0.0, realMath);
        // VecN
        var listInt : seq<int> := [9,0,2,4];
        var vNint:= new VecN<int>(listInt, intMath);
        var listReal: seq<real> := [0.3, 5.4, 5.0,7.5,5.0,6.0];
        var vNreal:= new VecN<real>(listReal, realMath);

        // test matrix
        // Mat2
        var m2IList : seq<seq<int>> := [[0,1],[1, 0]];
        var m2Int := new Mat2<int>(m2IList, intMath);
        var m2RList : seq<seq<real>> := [[0.0,1.1],[10.2, 0.8]];
        var m2Real := new Mat2<real>(m2RList, realMath);
        // Mat3
        var m3IList : seq<seq<int>> := [[0,1, 0],[1, 0, 0], [0,0,0]];
        var m3Int := new Mat3<int>(m3IList, intMath);
        var m3RList : seq<seq<real>> := [[0.0,1.1, 0.0],[10.2, 0.8, 0.0], [1.0, 1.0, 0.0]];
        var m3Real := new Mat3<real>(m3RList, realMath);
        // Mat34
        var m34IList : seq<seq<int>> := [[0,1, 0],[1, 0, 0], [0,0,0],[1, 0, 0]];
        var m34Int := new Mat34<int>(m34IList, intMath);
        var m34RList : seq<seq<real>> := [[0.0,1.1, 0.0],[10.2, 0.8, 0.0], [1.0, 1.0, 0.0] ,[10.2, 0.8, 0.0]];
        var m34Real := new Mat34<real>(m34RList, realMath);
        // Mat4
        var m4IList : seq<seq<int>> := [[0,1, 0, 0],[1, 0, 0, 1], [0,0,0, 0],[1, 0, 0, 0]];
        var m4Int := new Mat4<int>(m4IList, intMath);
        var m4RList : seq<seq<real>> := [[0.0,1.1, 0.0, 0.1],[10.2, 0.8, 0.0, 8.0], [1.0, 1.0, 0.0, 9.0] ,[10.2, 0.8, 0.0, 8.0]];
        var m4Real := new Mat4<real>(m4RList, realMath);

    }
}
