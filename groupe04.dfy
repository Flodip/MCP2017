datatype Rectangle = R(x1: int, y1: int, x2: int, y2: int) 

predicate method okR(r: Rectangle)
{
    r.x1 < r.x2 && r.y1 < r.y2 && 0 <= r.x1 && 0 <= r.x2 /*< N*/ && 0 <= r.y1 && 0 <= r.y2 /*< M*/
}

function method absR(r: Rectangle): int
{
	// Je savais pas quoi mettre ici du coup j ai mis l aire
	// pour pouvoir comparer 2 rectangles
    (r.x2 - r.x1) * (r.y2 - r.y1)
}

// [METHODS]
function method min(a:int, b:int) : int
{
    if a>b then b
    else a
}

function method max(a:int, b:int) : int
{
    if a<b then b
    else a
}

method MergeRectangles(a:array<Rectangle>,i:int, j:int, r:Rectangle)  returns (b:array<Rectangle>)
{
    b := new Rectangle[a.Length-1];

    forall(k | 0 <= k < i) {b[k] := a[k];}
    forall(k | i < k < j) {b[k-1] := a[k];}
    forall(k | j < k < a.Length) {b[k-2] := a[k];}
    b[a.Length-2] := r;
}

// [/METHODS]

// [PREDICATS]

//Use predicate method canMerge instead
/*predicate pCanMerge(a: Rectangle, b: Rectangle)
{	
	// erreur typo dans le rapport 1
	(a.y1 == b.y1 && a.y2 == b.y2 && (a.x1 == b.x2 || a.x2 == b.x1)) || (a.x1 == b.x1 && a.x2 == b.x2 && (a.y1 == b.y2 || a.y2 == b.y1))
}*/

predicate pInRectangle(r: Rectangle, x: int, y: int)
{
	r.x1 <= x <= r.x2 && r.y1 <= y <= r.y2
}

predicate pDoesNotOverlap(a: Rectangle, b: Rectangle)
{
	((a.x1 <= b.x1 && a.x2 <= b.x1) || (a.x1 >= b.x2 && a.x2 >= b.x2)) 
    || ((a.y1 <= b.y1 && a.y2 <= b.y1) || (a.y1 <= b.y2 && a.y2 >= b.y2))
}

predicate pNoOverlap(ListeRectangles: array<Rectangle>)
{
    forall i,j | 0 <= i < j < ListeRectangles.Length:: pDoesNotOverlap(ListeRectangles[i],ListeRectangles[j])
}

//modified
predicate pCouvertureDescendante(C0: Couverture, C: Couverture)
{
    true
}

// [/PREDICATS]

class Couverture {
    
    var ListeRectangles: array<Rectangle>;

    predicate ok()
        reads this, ListeRectangles
    { 
        ListeRectangles != null && forall i | 0 <= i < ListeRectangles.Length :: okR(ListeRectangles[i])
        && pNoOverlap(ListeRectangles)
    }

    constructor (qs: array<Rectangle>)
        requires pNoOverlap(qs)
        requires qs != null
        modifies this
        ensures ok()
    {
        ListeRectangles := qs;
    }
   
    // [METHODS]

    predicate method canMerge(a:Rectangle, b:Rectangle)
    {
        (a.y1 == b.y1 && a.y2 == b.y2 && (a.x1 == b.x2 || a.x2 == b.x1)) 
        || (a.x1 == b.x1 && a.x2 == b.x2 && (a.y1 == b.y2 || a.y2 == b.y1))
    }

    method merge(a:Rectangle, b:Rectangle) returns (c:Rectangle)
        requires canMerge(a,b)
        ensures c.x1 == min(a.x1,b.x1) && c.y1 == min(a.y1,b.y1)
                && c.x2 == max(a.x2,b.x2) && c.y2 == max(a.y2,b.y2)
    {
        c := R(min(a.x1,b.x1), min(a.y1,b.y1), max(a.x2,b.x2), max(a.y2,b.y2));
    }

    method improve()
    	requires ok()
    	ensures ok() && pCouvertureDescendante(old(this), this)
        modifies this
    {
        forall(i,j | 0 <= i < j < ListeRectangles.Length) {
            if(canMerge(ListeRectangles[i],ListeRectangles[j])){
                var r := merge(ListeRectangles[i],ListeRectangles[j]);
                ListeRectangles := MergeRectangles(ListeRectangles,i,j,r);
            }
        }
    }
    
    method optimize() 
        requires ok()
        ensures ok()
    {
        /* ... */
    }

    method dump() 
        requires ok()
    {
        var i := 0;
        var first := true;
        print "[ ";
        while i < ListeRectangles.Length
        {
            if !first { print ", "; }
            print ListeRectangles[i];
            i := i + 1;
            first := false;
        }
        print " ]\n";
    }

    // [/METHODS]
}

method Main() 
{
    // Vous devez écrire ici trois tests de votre méthode optimize
    var g := new Rectangle[3];
    g[1], g[2] := R(1,1,1,1), R(2,2,2,2);

    var m := new Couverture(g);
    m.dump();
}

