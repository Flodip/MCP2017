
// Type de donnée Rectangle
// p1(x1, y1) et p2(x2, y2) les coordonnées des coins supérieur gauche et inférieur droit
datatype Rectangle = R(x1: int, y1: int, x2: int, y2: int) 

// Invariant de représentation de Rectangle
predicate method okR(r: Rectangle)
{
    r.x1 < r.x2 && r.y1 < r.y2 && 0 <= r.x1 && 0 <= r.x2 /*< N*/ && 0 <= r.y1 && 0 <= r.y2 /*< M*/
}

// Fonction d'abstraction de rectangle
// Aire du rectangle
function method absR(r: Rectangle): int
{
    (r.y2-r.y1)*(r.x2-r.x1)
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
    C0.nbRectangles >= C.nbRectangles
    && forall i | 0 <= i < C0.nbRectangles ::
        forall x, y | C0.ListeRectangles[i].x1 <= x <= C0.ListeRectangles[i].x2
                    && C0.ListeRectangles[i].y1 <= y <= C0.ListeRectangles[i].y2 ::
                        C.contains(x, y)
    && forall i | 0 <= i < C.nbRectangles ::
        forall x, y | C.ListeRectangles[i].x1 <= x <= C.ListeRectangles[i].x2
                    && C.ListeRectangles[i].y1 <= y <= C.ListeRectangles[i].y2 ::
                        C0.contains(x, y)
}

class Couverture {
    
    var ListeRectangles: array<Rectangle>; // liste des rectangles qui composent la couverture
    //ghost var Rectangles: set<Rectangle>; // abstraction de l'ensemble des rectangles
    var nbRectangles: int; // nombre de rectangles de la couverture

    // Invariant de représentation et fonction d'abstraction de Couverture
    predicate valid()
        reads this, ListeRectangles
    { 
        // ok
        ListeRectangles != null &&
        0 <= nbRectangles <= ListeRectangles.Length
        
        // abs
        // pas encore utilise
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

        // abstraction Rectangles pas utilise dans cette partie du projet
        //Rectangles := {};
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

    // Ajoute le rectangle résultant de la fusion des rectangles aux positions i et j
    // de ListeRectangles et supprime ceux-ci
    method MergeRectangles(i:int, j:int, r:Rectangle) returns (lr: array<Rectangle>)
        requires valid()
        requires 0 <= i < j < nbRectangles
        requires nbRectangles > 1
        ensures lr != null && 0 <= lr.Length && lr.Length == nbRectangles-1 && fresh(lr)
        ensures lr[i] == r // le nouveau rectanle (fusion des rectangles i et j) est mis a l'indice i
        // tous les rectangles de la couverture sont copies dans la nouvelle liste sauf les indices i et j
        ensures forall l | 0 <= l < i :: lr[l] == ListeRectangles[l]
        ensures forall l | i < l < j :: lr[l] == ListeRectangles[l]
        ensures forall l | j < l < nbRectangles-1 :: lr[l] == ListeRectangles[l+1]
{
        var k := 0;
        lr := new Rectangle[nbRectangles-1];

        while k < i
            invariant 0 <= k <= i
            invariant forall l | 0 <= l < k :: lr[l] == ListeRectangles[l]
    
            decreases i-k
        {
            lr[k] := ListeRectangles[k];
            k := k+1;
        }

        lr[k] := r;
        assert lr[i] == r;
        k := k+1;

        while k < j
            invariant i < k <= j
            invariant lr[i] == r
            invariant forall l | 0 <= l < i :: lr[l] == ListeRectangles[l]
            invariant forall l | i < l < k :: lr[l] == ListeRectangles[l]
            decreases j-k
        {
            lr[k] := ListeRectangles[k];
            k := k+1;
        }

        while k < nbRectangles-1
            invariant 0 <= j <= k < nbRectangles
            invariant lr[i] == r
            invariant forall l | 0 <= l < i :: lr[l] == ListeRectangles[l]
            invariant forall l | i < l < j :: lr[l] == ListeRectangles[l]
            invariant forall l | j < l < k :: lr[l] == ListeRectangles[l+1]
            decreases nbRectangles-k
        {
            lr[k] := ListeRectangles[k+1];
            k := k+1;
        }
    }

    // Retourne le rectangle résultant de la fusion des rectangles a et b
    method merge(a:Rectangle, b:Rectangle) returns (c:Rectangle)
        requires canMerge(a,b)
    {
        c := R(min(a.x1,b.x1), min(a.y1,b.y1), max(a.x2,b.x2), max(a.y2,b.y2));
    }

    // Essaye d'améliorer la couverture
    // Retourne true <==> la couverture est améliorée
    method improve() returns (b:bool)
        requires valid()
        ensures valid()
        ensures pCouvertureDescendante(this, old(this))
        ensures b <==> nbRectangles < old(nbRectangles)
        modifies this
    {
        var i := 0;
        b := false;

        while i < nbRectangles
            invariant valid()
            invariant nbRectangles <= old(nbRectangles)
            invariant b <==> nbRectangles < old(nbRectangles)
            decreases old(nbRectangles)-i
        {
            var j := i+1;
            while j < nbRectangles
                invariant valid()
                invariant nbRectangles <= old(nbRectangles)
                invariant b <==> nbRectangles < old(nbRectangles)
                decreases old(nbRectangles)-j
            {
                if canMerge(ListeRectangles[i],ListeRectangles[j]) {
                    var r := merge(ListeRectangles[i],ListeRectangles[j]);
                    ListeRectangles := MergeRectangles(i,j,r);
                    nbRectangles := nbRectangles-1;
                    b := true;
                }
                assert b <==> nbRectangles < old(nbRectangles);
                j := j+1;
            }
            i := i+1;
        }
    }


    // Calcule une couverture localement optimale
    method optimize() 
        requires valid()
        modifies this
        ensures valid()
        ensures pCouvertureDescendante(old(this), this)
    {
        var size := nbRectangles;
        var canStillImprove := true;
        var i := 0;
        while canStillImprove && i < size
            invariant valid()
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

