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

//modified
predicate pCouvertureDescendante(C0: Couverture, C: Couverture)
{
    //Prochaine partie du projet
    true
}

// [/PREDICATS]

class Couverture {
    
    var ListeRectangles: array<Rectangle>;
    //Ajout d'une variable dans la classe couverture pour retenir le nombre de rectangles
    //dans la liste, la taille du tableau pouvant être supérieure au nombre de rectangles
    var nbRectangles: int;
    //abstraction de ListRectangles
    ghost var Rectangles: set<Rectangle>;

    predicate valid()
        reads this, ListeRectangles
    {
        //ok
        ListeRectangles != null
        && 0 <= nbRectangles <= ListeRectangles.Length
        && forall i | 0 <= i < nbRectangles :: okR(ListeRectangles[i])
        && pNoOverlap(ListeRectangles) 
        //abs
        && |Rectangles| == nbRectangles
        && forall rect | rect in Rectangles
            :: exists j | 0 <= j < nbRectangles :: rect == ListeRectangles[j]
    }

    constructor (qs: array<Rectangle>)
        requires pNoOverlap(qs)
        requires qs != null
        requires forall i | 0 <= i < qs.Length :: okR(qs[i])
        modifies this, ListeRectangles
        ensures valid()
    {
        ListeRectangles := qs;
        nbRectangles := qs.Length;
        Rectangles := {};
        forall i | 0 <= i < nbRectangles {Rectangles := Rectangles + {ListeRectangles[i]};}
    }
   
    // [METHODS ]

    predicate method canMerge(a:Rectangle, b:Rectangle)
    {
        (a.y1 == b.y1 && a.y2 == b.y2 && (a.x1 == b.x2 || a.x2 == b.x1)) 
        || (a.x1 == b.x1 && a.x2 == b.x2 && (a.y1 == b.y2 || a.y2 == b.y1))
    }

    method MergeRectangles(a:array<Rectangle>,i:int, j:int, r:Rectangle)
        modifies a;
    {
        // abs, on retire au set le rectangle i et rectangle j et on ajoute leur merge
        Rectangles := Rectangles - {a[i],a[j]} + {r};
        // /abs

        forall(k | i < k < j) {a[k] := a[k+1];}
        forall(k | j < k < nbRectangles) {a[k-1] := a[k];}

        nbRectangles := nbRectangles - 1;
        a[nbRectangles-1] := r;
    }

    method merge(a:Rectangle, b:Rectangle) returns (c:Rectangle)
        requires canMerge(a,b)
        ensures c.x1 == min(a.x1,b.x1) && c.y1 == min(a.y1,b.y1)
                && c.x2 == max(a.x2,b.x2) && c.y2 == max(a.y2,b.y2)
    {
        c := R(min(a.x1,b.x1), min(a.y1,b.y1), max(a.x2,b.x2), max(a.y2,b.y2));
    }

    method improve() returns (b:bool)
    	requires valid()
    	ensures valid() && pCouvertureDescendante(old(this), this)
        modifies this
    {
        var i := 0;
        var j := 0;
        b := false;

        while  i<nbRectangles {
            while  j<nbRectangles {
                if canMerge(ListeRectangles[i],ListeRectangles[j]) {
                    var r := merge(ListeRectangles[i],ListeRectangles[j]);
                    MergeRectangles(ListeRectangles,i,j,r);
                    b := true;
                }
                j := j+1;
            }
            i := i+1;
        }
    }
    
    method optimize() 
        requires valid()
        ensures valid()
    {
        var canStillImprove := true;
        while canStillImprove { canStillImprove := improve();}
    }

    method dump() 
        requires valid()
    {
        var i := 0;
        var first := true;
        print "[ ";
        while i < nbRectangles
        {
            if !first { print ", "; }
            print ListeRectangles[i];
            i := i + 1;
            first := false;
        }
        print " ]\n";
    }

    // [/METHODS]

    // [PREDICATES]
    predicate pNoOverlap(ListeRectangles: array<Rectangle>)
    {
        forall i,j | 0 <= i < j < nbRectangles :: pDoesNotOverlap(ListeRectangles[i],ListeRectangles[j])
    }
    // [/PREDICATES]
}

method Main() 
{
    // Vous devez écrire ici trois tests de votre méthode optimize
    var g := new Rectangle[3];
    g[1], g[2] := R(1,1,1,1), R(2,2,2,2);

    var m := new Couverture(g);
    m.dump();
}

