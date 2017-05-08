
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

predicate pInRectangle(r: Rectangle, x: int, y: int)
{
    r.x1 <= x <= r.x2 && r.y1 <= y <= r.y2
}

predicate pDoesNotOverlap(a: Rectangle, b: Rectangle)
{
    ((a.x1 <= b.x1 && a.x2 <= b.x1) || (a.x1 >= b.x2 && a.x2 >= b.x2)) 
    || ((a.y1 <= b.y1 && a.y2 <= b.y1) || (a.y1 <= b.y2 && a.y2 >= b.y2))
}

predicate pCouvertureDescendante(C0: Couverture, C: Couverture)
{
    //Prochaine partie du projet
    true
}

class Couverture {
    
    var ListeRectangles: array<Rectangle>; // liste des rectangles qui composent la couverture
    ghost var Rectangles: set<Rectangle>; // abstraction de l'ensemble des rectangles
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
    {
        ListeRectangles := qs;
        nbRectangles := qs.Length;

        // abstraction Rectangles pas utilise dans cette partie du projet
        Rectangles := {};
    }

    predicate method canMerge(a:Rectangle, b:Rectangle)
    {
        (a.y1 == b.y1 && a.y2 == b.y2 && (a.x1 == b.x2 || a.x2 == b.x1)) 
        || (a.x1 == b.x1 && a.x2 == b.x2 && (a.y1 == b.y2 || a.y2 == b.y1))
    }

    // Ajoute le rectangle résultant de la fusion des rectangles aux positions i et j
    // de ListeRectangles et supprime ceux-ci
    method MergeRectangles(i:int, j:int, r:Rectangle) 
        requires valid()
        requires 0 <= i < j < nbRectangles
        requires nbRectangles > 1
        modifies ListeRectangles
    {
        ListeRectangles[i] := r;

        var k := j;
        while k < nbRectangles-1
            invariant nbRectangles > 1
            invariant valid()
            invariant 0 <= j <= k < nbRectangles
            decreases nbRectangles-k
        {
            ListeRectangles[k] := ListeRectangles[k+1];
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
        modifies this, ListeRectangles
    {
        var i := 0;
        b := false;

        while i < nbRectangles
            invariant valid()
            invariant nbRectangles <= old(nbRectangles)
            decreases old(nbRectangles)-i
        {
            var j := i+1;
            while j < nbRectangles
                invariant valid()
                invariant nbRectangles <= old(nbRectangles)
                decreases old(nbRectangles)-j
            {
                if canMerge(ListeRectangles[i],ListeRectangles[j]) {
                    var r := merge(ListeRectangles[i],ListeRectangles[j]);
                    MergeRectangles(i,j,r);
                    nbRectangles := nbRectangles-1;
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
        ensures valid()
    {
        var canStillImprove := true;
        while canStillImprove
        { 
            canStillImprove := improve();
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
    // Test 1

    print "Test 1 : pas de merge\n";

    var g := new Rectangle[2];
    g[0], g[1] := R(1,1,2,2), R(5,5,7,7);

    var m := new Couverture(g);

    m.dump();
    m.optimize();
    m.dump();

    // Test 2

    print "Test 2 : merge\n";

    g := new Rectangle[2];
    g[0], g[1] := R(1,1,2,2), R(2,1,3,2);

    m := new Couverture(g);

    m.dump();
    m.optimize();
    m.dump();

    // Test 3

    print "Test 3 : plusieurs merge\n";

    g := new Rectangle[4];
    g[0], g[1], g[2], g[3] := R(0,0,2,2), R(2,0,4,2), R(2,2,4,4), R(6,6,8,8);

    m := new Couverture(g);

    m.dump();
    m.optimize();
    m.dump();
}

