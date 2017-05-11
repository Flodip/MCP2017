datatype Point = P(x: int, y: int)
// Type de donnée Rectangle
// p1(x1, y1) et p2(x2, y2) les coordonnées des coins supérieur gauche et inférieur droit
datatype Rectangle = R(x1: int, y1: int, x2: int, y2: int) 

// Invariant de représentation de Rectangle
predicate method okR(r: Rectangle)
{
    r.x1 < r.x2 && r.y1 < r.y2 && 0 <= r.x1 && 0 <= r.x2 && 0 <= r.y1 && 0 <= r.y2
}

// Fonction d'abstraction de rectangle
function method abs(q: Rectangle): set<Point>
{ 
    set x, y | q.x1 <= x < q.x2 && q.y1 <= y < q.y2 :: Point.P(x, y) 
}

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

predicate method pInRectangle(r: Rectangle, x: int, y: int)
{
    r.x1 <= x <= r.x2 && r.y1 <= y <= r.y2
}

predicate pDoesNotOverlap(a: Rectangle, b: Rectangle)
{
    ((a.x1 <= b.x1 && a.x2 <= b.x1) || (a.x1 >= b.x2 && a.x2 >= b.x2)) 
    || ((a.y1 <= b.y1 && a.y2 <= b.y1) || (a.y1 <= b.y2 && a.y2 >= b.y2))
}

predicate pCouvertureDescendante(C0: Couverture, C: Couverture)
    requires C0 != null && C != null
    requires C0.valid() && C.valid()
    reads C0, C0.ListeRectangles, C, C.ListeRectangles
{
    forall x, y :: C.contains(x,y) <==> C0.contains(x,y)    
}

class Couverture {
    
    var ListeRectangles: array<Rectangle>; // liste des rectangles qui composent la couverture
    var nbRectangles: int; // nombre de rectangles de la couverture

    // Invariant de représentation
    predicate valid()
        reads this, ListeRectangles
    { 
        ListeRectangles != null &&
        0 <= nbRectangles <= ListeRectangles.Length
    }

    // Constructeur de la classe
    // Initialise la couverture avec les rectangles du tableau qs
    constructor (qs: array<Rectangle>)
        requires qs != null
        modifies this
        ensures valid()
        ensures ListeRectangles == qs
        ensures nbRectangles == qs.Length
    {
        ListeRectangles := qs;
        nbRectangles := qs.Length;
    }

    predicate method contains(x:int, y:int)
        requires valid()
        reads this, ListeRectangles
    {
        exists i | 0 <= i < nbRectangles :: pInRectangle(ListeRectangles[i], x, y)
    }

    predicate method canMerge(a:Rectangle, b:Rectangle)
    {
        (a.y1 == b.y1 && a.y2 == b.y2 && (a.x1 == b.x2 || a.x2 == b.x1)) 
        || (a.x1 == b.x1 && a.x2 == b.x2 && (a.y1 == b.y2 || a.y2 == b.y1))
    }

    method MergeRectangles(i:int, j:int, r:Rectangle)
        requires valid()
        requires 0 <= i < j < nbRectangles
        modifies ListeRectangles, this
        ensures ListeRectangles == old(ListeRectangles)
        ensures 0 <= nbRectangles == old(nbRectangles) - 1 < old(nbRectangles)
        ensures valid()
    {
        ListeRectangles[i] := r;
        if (j < nbRectangles - 1) {
            ListeRectangles[j] := ListeRectangles[nbRectangles-1];
        }
        nbRectangles := nbRectangles - 1;
    }
    // Retourne le rectangle résultant de la fusion des rectangles a et b
    method merge(a:Rectangle, b:Rectangle) returns (c:Rectangle)
        requires canMerge(a,b)
        ensures abs(a) + abs(b) == abs(c)
    {
        c := R(min(a.x1,b.x1), min(a.y1,b.y1), max(a.x2,b.x2), max(a.y2,b.y2));
    }

    // Essaye d'améliorer la couverture
    // Retourne true <==> la couverture est améliorée
    method improve() returns (b:bool)
        requires valid()
        modifies this, ListeRectangles
        ensures valid()
        ensures pCouvertureDescendante(this, old(this))
        ensures b <==> nbRectangles < old(nbRectangles)
        ensures ListeRectangles == old(ListeRectangles)
    {
        var i := 0;
        b := false;

        while i < nbRectangles
            invariant valid()
            invariant nbRectangles <= old(nbRectangles)
            invariant b <==> nbRectangles < old(nbRectangles)
            invariant ListeRectangles == old(ListeRectangles)
            decreases old(nbRectangles)-i
        {
            var j := i+1;
            while j < nbRectangles
                invariant valid()
                invariant nbRectangles <= old(nbRectangles)
                invariant b <==> nbRectangles < old(nbRectangles)
                invariant ListeRectangles == old(ListeRectangles)
                decreases old(nbRectangles)-j
            {
                if canMerge(ListeRectangles[i],ListeRectangles[j]) {
                    var r := merge(ListeRectangles[i],ListeRectangles[j]);
                    MergeRectangles(i,j,r);
                    b := true;
                }
                
                j := j+1;
            }
            i := i+1;
        }
    }


    // Calcule une couverture localement optimale
    method optimize() 
        requires valid()
        modifies this, ListeRectangles
        ensures valid()
        ensures pCouvertureDescendante(old(this), this)
    {
        var size := nbRectangles;
        var canStillImprove := true;
        var i := 0;
        while canStillImprove && i < size
            invariant valid()
            invariant ListeRectangles == old(ListeRectangles)
            decreases size - i
        { 
            canStillImprove := improve();
            i := i+1;
        }
    }

    // Imprime la liste de rectangles
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
}

method Main() 
{
    //Test 1

    print "Test 1 : pas de merge\n";

    var g := new Rectangle[2];
    g[0], g[1] := R(1,1,2,2), R(5,5,7,7);

    var m := new Couverture(g);

    m.dump();
    m.optimize();
    m.dump();

    //Test 2

    print "Test 2 : merge\n";

    g := new Rectangle[2];
    g[0], g[1] := R(1,1,2,2), R(2,1,3,2);

    m := new Couverture(g);

    m.dump();
    m.optimize();
    m.dump();

    //Test 3

    print "Test 3 : plusieurs merge\n";

    g := new Rectangle[4];
    g[0], g[1], g[2], g[3] := R(0,0,2,2), R(2,0,4,2), R(0,2,4,4), R(6,6,8,8);

    m := new Couverture(g);

    m.dump();
    m.optimize();
    m.dump();
}

