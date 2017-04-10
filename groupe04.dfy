
// Le type de données pour les rectangles.
// Remplacez-le par votre définition de rectangle.
// Vous pouvez en introduire d'autres si vous le jugez pertinent.
datatype TrucACinqInts = MonTrucQuiAPasLeBonNom(a: int, b: int, c: int, d: int, e: int) 

predicate method okTruc(t: TrucACinqInts)
{
    t.a == t.b*2 == t.c*3 == t.d*4 == t.e*5
}

function method absTruc(t: TrucACinqInts): int
{
    t.e / 5
}

class Couverture {
    
    var monTableauDeRectanglesAvecUnNomTropLongAChangerDOffice: array<TrucACinqInts>;
    // autres champs de la classe

    // Ceci est votre invariant de représentation.
    // C'est plus simple d'avoir ok() dans les pre et les posts que le le recoper à chaque fois.
    predicate ok()
        reads this, monTableauDeRectanglesAvecUnNomTropLongAChangerDOffice
    { 
        monTableauDeRectanglesAvecUnNomTropLongAChangerDOffice != null
    }

    constructor (qs: array<TrucACinqInts>)
        // ...
        requires qs != null
        modifies this // forcément ;-)
        ensures ok()
    {
        monTableauDeRectanglesAvecUnNomTropLongAChangerDOffice := qs;
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
        while i < monTableauDeRectanglesAvecUnNomTropLongAChangerDOffice.Length
        {
            if !first { print ", "; }
            print monTableauDeRectanglesAvecUnNomTropLongAChangerDOffice[i];
            i := i + 1;
            first := false;
        }
        print " ]\n";
    }
}

method Main() 
{
    // Vous devez écrire ici trois tests de votre méthode optimize
    var g := new TrucACinqInts[3];
    g[1], g[2] := MonTrucQuiAPasLeBonNom(1,1,1,1,1), MonTrucQuiAPasLeBonNom(2,2,2,2,2);

    var m := new Couverture(g);
    m.dump();
}

