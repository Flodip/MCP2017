// Différence Partie 1: Dans la spécification on a écrit type Couverture et on passait Couverture en paramètre aux méthodes
//		Ici, on fait avec une classe donc les déclarations des méthodes changent

// Il ne faut pas les post pour cette remise mais on garde certains d'entre-eux en commentaire pour la suite
// (pas forcèment correct pour le moment)
datatype Rectangle = Rectangle(x: int, y: int, w: int, h: int)
datatype Inside = Null | Single(Rectangle) // Différence Partie 1: Type de retour pour la méthode contains - datatype null pas permis

predicate okRect(r: Rectangle)
{
  r.x >= 0 && r.y >= 0 && r.w > 0 && r.h > 0
}

// seq<seq<>> car l'ordre a de l'importance: on sait retrouver le placement d'un point dans le rectangle ainsi que le x,y d'un point
function method absRect(r: Rectangle): seq<seq<int>>
ensures |absRect(r)| == 4 && forall i :: 0 <= i < |absRect(r)| ==> |absRect(r)[i]| == 2
{
  [[r.x, r.y],[r.x + r.w, r.y],[r.x, r.y + r.h],[r.x + r.w, r.y + r.h]]
}

// Ordre total strict sur les rectangles: true si r1 < r2, false sinon
function method le(r1: Rectangle, r2: Rectangle): bool
{
  if r1.y != r2.y then r1.y < r2.y else r1.x < r2.x
}

predicate intersecting(r1: Rectangle, r2: Rectangle)
{
  r1.x <= (r2.x + r2.w) && (r1.x + r1.w) >= r2.x && r1.y >= (r2.y + r2.h) && (r1.y + r1.h) <= r2.y
}

// True si 2 rectangles se superposent, false sinon (côte à côte accepté)
predicate intersectingAbs(r1: Rectangle, r2: Rectangle)
requires |absRect(r1)| == 4 && |absRect(r2)| == 4
{
  getX(topLeft(absRect(r1))) <= getX(topRight(absRect(r2))) &&
  getX(topRight(absRect(r1))) >= getX(topLeft(absRect(r2))) &&
  getY(topLeft(absRect(r1))) >= getY(bottomLeft(absRect(r2))) &&
  getY(bottomLeft(absRect(r1))) <= getY(topLeft(absRect(r2)))
}

// True si le point (x, y) est dans le rectangle r
function method inRectangle(x : int, y : int, r : Rectangle): bool
{
  r.x <= x <= r.x + r.w && 	// abcisse du point dans le rectangle
  r.y <= y <= r.y + r.h	// ordonnée du point dans le rectangle
}

method cmp(x : int, y : int, r : Rectangle) returns (s : int)
{
  if inRectangle(x, y, r) { return 0; }
  else {
    // utiliser l'ordre partiel (défini sur les rectangles) pour déterminer la position du point par rapport à r
    var r2 := Rectangle(x, y, 1, 1); // On crée un rectangle de taille 1 pour réutiliser directement le(Rectangle, Rectangle), on pourrait faire le(Rectangle, Point)
    if (le(r, r2)) { return -1; }
    else { return 1; }
  }
}

function topLeft(rect : seq<seq<int>>) : seq<int> requires |rect| == 4 { rect[0] }

function topRight(rect : seq<seq<int>>) : seq<int> requires |rect| == 4 { rect[1] }

function bottomLeft(rect : seq<seq<int>>) : seq<int> requires |rect| == 4 { rect[2] }

function bottomRight(rect : seq<seq<int>>) : seq<int> requires |rect| == 4 { rect[3] }

function getX(point : seq<int>) : int requires |point| == 2 { point[0] }

function getY(point : seq<int>) : int requires |point| == 2 { point[1] }

function aire(rect : Rectangle) : int { rect.w * rect.h }

// Transforme une seq vers un set (pre faut que il n'y a pas d'éléments identiques)
function method seq2set<T> (s:seq<T>): set<T>
{
  if s == [] then {}
    else {s[0]} + seq2set(s[1..])
  }

  function mapToAbs(tabRect: array<Rectangle>, i: int) : seq<seq<seq<int>>>
  requires tabRect != null && 0 <= i < tabRect.Length
  reads tabRect
  {
    if i == 0 || tabRect.Length == 0 then []
    else [absRect(tabRect[i])] + mapToAbs(tabRect, i-1)
  }

  class Couverture {

    var tabRect: array<Rectangle>;
    ghost var absCouv: seq<seq<seq<int>>>;

    // Invariant de représentation
    predicate ok()
    reads this, tabRect
    {
      tabRect != null &&
      tabRect.Length >= 0 &&
      forall i | 0 <= i < tabRect.Length :: okRect(tabRect[i]) &&
      sorted(tabRect) &&
      forall i, j :: 0 <= i < tabRect.Length && i < j < tabRect.Length ==> tabRect[i] != tabRect[j] &&
      forall i, j :: 0 <= i < tabRect.Length && i < j < tabRect.Length ==> !intersecting(tabRect[i], tabRect[j])
    }

    predicate abs()
    requires tabRect != null && tabRect.Length >= 0
    reads this, tabRect
    {
      tabRect != null &&
      tabRect.Length == |absCouv| &&
      forall i :: 0 <= i < tabRect.Length ==> inCouverture(tabRect[i]) &&
      forall i, j :: 0 <= i < tabRect.Length && i < j < tabRect.Length ==> !intersectingAbs(tabRect[i], tabRect[j])
    }

    predicate valid()
    reads this, tabRect
    {
      this.ok() && this.abs()
    }

    // Différence Partie 1 : ajout inCouverture
    predicate inCouverture(r: Rectangle)
    reads this, tabRect
    {
      absRect(r) in absCouv
    }

    constructor (tr: array<Rectangle>)
    requires tr != null && tr.Length > 0 &&
    forall i | 0 <= i < tr.Length :: okRect(tr[i]) &&
    forall i, j :: 0 <= i < tr.Length && i < j < tr.Length ==> !intersecting(tr[i], tr[j])
    modifies this
    ensures tabRect != null
    {
      var newTabRect := new Rectangle[tr.Length];
      var i := 0;
      while (i < tr.Length){
        newTabRect[i] := tr[i];
        i := i + 1;
      }
      sort(newTabRect);
      tabRect := newTabRect;
      absCouv := mapToAbs(tabRect, tabRect.Length-1);
    }

    method optimize()
    requires tabRect != null
    decreases *
    modifies this
    ensures tabRect != null
    {
      var isLocalOpti := localOpti();
      while(!isLocalOpti && tabRect.Length > 1)
      decreases *
      invariant tabRect != null
      invariant tabRect.Length <= old(tabRect.Length)
      {
        improve();
        isLocalOpti := localOpti();
      }
    }

    method canMerge(a : Rectangle, b : Rectangle) returns (f : bool)
    {
      return adj(a,b);
    }

    // Fusionne b vers a
    method merge(a : Rectangle, b : Rectangle) returns (f : Rectangle)
    {
      var base := a;
      var other := b;
      var aBeforeB := le(a,b);

      if(!aBeforeB) {
        // Inverser si jamais b < a
        base := b;
        other := a;
      }

      var sameX := base.x == other.x;
      if(sameX) { // Sur la même colonne
        f := Rectangle(base.x, base.y, base.w, base.h + other.h);
        } else { // Sur la même ligne
          f := Rectangle(base.x, base.y, base.w + other.w, base.h);
        }
      }

      method improve()
      requires tabRect != null && tabRect.Length > 1
      modifies this
      decreases *
      ensures tabRect != null && tabRect.Length <= old(tabRect.Length)
      {
        var i := 0;
        while(i < (tabRect.Length)-1)
        invariant tabRect != null
        invariant tabRect.Length <= old(tabRect.Length)
        invariant 0 <= i <= tabRect.Length
        decreases *
        {
          var canMergeTest := canMerge(tabRect[i], tabRect[i+1]);
          if(canMergeTest){
            var mergedRect := merge(tabRect[i], tabRect[i+1]);
            var removed := removeAndReplace(mergedRect, i);
          }
          i := i + 1;
        }
      }

      // Replaces tabRect[index] with rectNew and removes tabRect[index+1],
      // tabRect is new shrinked array, returns removed Rectangle
      method removeAndReplace(rectNew: Rectangle, index : int) returns (r: Rectangle)
      requires tabRect != null && tabRect.Length >= 2 && 0 <= index < tabRect.Length-1 // -1 because we check index && index+1
      modifies this
      ensures fresh(tabRect) && tabRect != null && tabRect.Length == old(tabRect.Length)-1
      {
        var newLength := tabRect.Length-1;
        var newTabRect := new Rectangle[newLength];
        var i := 0;
        var j := 0;
        var length := tabRect.Length;
        while(i < length && j < newLength)
        invariant 0 <= i <= length
        invariant j <= i
        invariant tabRect == old(tabRect)
        invariant 0 <= j <= newLength
        {
          if(i == index) {
            newTabRect[j] := rectNew;
            j := j + 1;
            } else if (i == index+1) {
              r := tabRect[i];
              } else {
                newTabRect[j] := tabRect[i];
                j := j + 1;
              }
              i := i + 1;
            }
            tabRect := newTabRect;
          }

          // BinarySearch adapté depuis http://rise4fun.com/Dafny/tutorial
          method contains(x : int, y : int) returns (r : Inside)
          requires tabRect != null && x >= 0 && y >= 0
          {
            var low, high := 0, tabRect.Length;
            while low < high
            invariant 0 <= low <= high <= tabRect.Length
            {
              var mid := (low + high) / 2;
              var cmp := cmp(x, y, tabRect[mid]);
              if cmp > 0 // tabRect[mid] < value : point situé après le rectangle
              {
                low := mid + 1;
              }
              if cmp < 0 // value < tabRect[mid] : point situé avant le rectangle
              {
                high := mid;
              }
              else	// point dans le rectangle
              {
                return Single(tabRect[mid]);
              }
            }
            assert high >= low;
            return Null;
          }

          // On convertit vers une seq pour faire l'intersection, absRect ensures que les éléments sont uniques
		  // https://github.com/Microsoft/dafny/issues/82
		  // multiset(s) marche pas car |multiset(s)| donne une erreur (apparamment Length pas défini pour les multisets)
          predicate method adj(r0: Rectangle, r1: Rectangle)
          {
            |seq2set<seq<int>>(absRect(r0)) * seq2set<seq<int>>(absRect(r1))| == 2
          }

          // On utilise un predicate method pour simplifier les expressions:
          //	sinon il faut un predicate qui définit adj par rapport à absCouv (set de 4 points)
          //  et une autre méthode qui définit adj pour 2 Rectangle
          predicate method localOpti()
          requires tabRect != null
          reads this, tabRect
          {
            forall i, j :: 0 <= i < tabRect.Length && i < j < tabRect.Length ==> !adj(tabRect[i], tabRect[j])
          }

          predicate sorted(a: array<Rectangle>)
          requires a != null
          reads a
          {
            forall i, j | 0 <= i <= j < a.Length :: le(a[i],a[j])
          }

          method sort(a: array<Rectangle>)
          requires a != null
          modifies a
          {
            var i := a.Length;
            while (i > 0)
            {
              var j := 0;
              while (j < i - 1)
              {
                if (le(a[j + 1],a[j])) {
                  a[j], a[j+1] := a[j+1], a[j];
                }
                j := j + 1;
              }
              i := i - 1;
            }
          }

          method dump()
          requires tabRect != null
          {
            var i := 0;
            var first := true;
            print "[ ";
            while i < tabRect.Length
            {
              if !first { print ",\n"; }
              print tabRect[i];
              i := i + 1;
              first := false;
            }
            print " ]\n";
          }
        }

        method Main()
        decreases *
        {
          // Vous devez écrire ici trois tests de votre méthode optimize

          // Test: couverture entièrement composée de 9 carrés de 1x1
          // optimisée en un seul carré de 3x3 commençant au point (0,0)
          print "\nTEST----------------------------------------------------------\n";
          var rectArray := new Rectangle[9];
          rectArray[0], rectArray[1], rectArray[2] := Rectangle(0, 0, 1, 1), Rectangle(0, 1, 1, 1), Rectangle(0, 2, 1, 1);
          rectArray[3], rectArray[4], rectArray[5] := Rectangle(1, 0, 1, 1), Rectangle(1, 1, 1, 1), Rectangle(1, 2, 1, 1);
          rectArray[6], rectArray[7], rectArray[8] := Rectangle(2, 0, 1, 1), Rectangle(2, 1, 1, 1), Rectangle(2, 2, 1, 1);

          var couv := new Couverture(rectArray);
          print "Couverture initiale:\n";
          couv.dump();
          couv.optimize();
          print "Couverture optimisée:\n";
          couv.dump();

          // Test      Couverture 9x9
          print "\nTEST----------------------------------------------------------\n";
          var rectArray2 := new Rectangle[8];
          rectArray2[0], rectArray2[1], rectArray2[2] := Rectangle(0, 0, 1, 1), Rectangle(0, 1, 1, 1), Rectangle(0, 2, 1, 1);
          rectArray2[3],                rectArray2[4] := Rectangle(1, 0, 1, 1),                        Rectangle(1, 2, 1, 1);
          rectArray2[5], rectArray2[6], rectArray2[7] := Rectangle(2, 0, 1, 1), Rectangle(2, 1, 1, 1), Rectangle(2, 2, 1, 1);

          var couv2 := new Couverture(rectArray2);
          print "Couverture initiale:\n";
          couv2.dump();
          couv2.optimize();
          print "Couverture optimisée:\n";
          couv2.dump();

          // Test      Couverture 25x25
          print "\nTEST----------------------------------------------------------\n";
          var rectArray3 := new Rectangle[12];
          rectArray3[0], rectArray3[1], rectArray3[2] := Rectangle(0, 0, 1, 2), Rectangle(0, 3, 1, 1), Rectangle(1, 0, 3, 1);
          rectArray3[3], rectArray3[4], rectArray3[5] := Rectangle(3, 1, 1, 1), Rectangle(1, 1, 2, 1), Rectangle(1, 3, 1, 2);
          rectArray3[6], rectArray3[7], rectArray3[8] := Rectangle(2, 4, 1, 1), Rectangle(2, 2, 2, 1), Rectangle(3, 3, 1, 1);
          rectArray3[9], rectArray3[10], rectArray3[11] := Rectangle(4, 2, 1, 1), Rectangle(3, 4, 2, 1), Rectangle(4, 3, 1, 1);

          var couv3 := new Couverture(rectArray3);
          print "Couverture initiale:\n";
          couv3.dump();
          couv3.optimize();
          print "Couverture optimisée:\n";
          couv3.dump();
        }
