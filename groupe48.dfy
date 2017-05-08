/*
 * Classe représentant un rectangle, ne contient que 4 variables, correspondant
 * à la position et aux dimensions du rectangle. Les méthodes de cette classe
 * sont soit des getters, soit des fonctions liées à l'affichage du rectangle.
 * Le contenu de cette classe n'est pas commenté.
 */

class Rectangle
{
    //attributes
    var x: int;
    var y: int;
    var width: int;
    var height: int;

    //predicates

    predicate ok()
        reads this
    {
        true
    }

    //constructor

    constructor (x: int, y: int, width: int, height: int)
        ensures ok()
        modifies this
    {
        this.x := x;
        this.y := y;
        this.width := width;
        this.height := height;
    }

    //methods

    method getX()
        returns (k: int)
        requires ok()
    {
        k := x;
    }

    method getY()
        returns (k: int)
        requires ok()
    {
        k := y;
    }

    method getWidth()
        returns (k: int)
        requires ok()
    {
        k := width;
    }

    method getHeight()
        returns (k: int)
        requires ok()
    {
        k := height;
    }

    method copy()
        returns (r: Rectangle)
        ensures r != null
    {
        r := new Rectangle(x, y, width, height);
    }

    method dump()
        requires ok()
    {
        print("Rectangle(");
        print(x);
        print(", ");
        print(y);
        print(", ");
        print(width);
        print(", ");
        print(height);
        print(")");
    }

    method customDump()
        requires ok()
    {
        print(x);
        print (" ");
        print (y);
        print (" ");
        print (width);
        print (" ");
        print (height);
        print ("\n");
    }
}

/*
 * Classe représentant un ensemble de rectangles, les différentes fonctions de
 * la classe sont commentées.
 */

class Couverture
{
    //attributes

    var rectangles: array<Rectangle>;
    var size: int;

    //predicates

    predicate ok()
        reads this
    {
        rectangles != null && 0 <= size <= rectangles.Length
    }

    //constructor

    constructor(rectangles: array<Rectangle>)
        requires rectangles != null
        ensures ok()
        modifies this
    {
        this.rectangles := rectangles;
        this.size := rectangles.Length;
    }

    //methods

    /*
     * Si il existe au moins deux rectangles de la couverture pouvant être
     * fusionnés, alors deux de ces rectangles sont fusionnés et le nombre de
     * rectangles diminue de 1.
     */
    method improve()
            requires ok()
            ensures ok()
            modifies this
    {
        //Il semble moins problématique de travailler sur une copie
        //(problème de preuve dans le cas contraire)
        var temp := new Rectangle[rectangles.Length];

        //on rempli la copie
        var k := 0;
        while (k < rectangles.Length)
            invariant rectangles != null
            invariant 0 <= k <= rectangles.Length
            invariant 0 <= size <= rectangles.Length
            invariant temp != null
            invariant rectangles.Length == temp.Length
            decreases rectangles.Length - k
        {
            temp[k] := rectangles[k];
            k := k + 1;
        }

        //on recherche des candidats à la fusion.
        var i := 0;
        while (i < temp.Length)
            invariant rectangles != null
            invariant 0 <= i <= rectangles.Length
            invariant 0 <= size <= rectangles.Length
            invariant temp != null
            invariant rectangles.Length == temp.Length
            decreases temp.Length - i;
        {
            if (temp[i] != null)
            {
                var j := i + 1;
                while (j < temp.Length)
                    invariant rectangles != null
                    invariant 0 <= i < j <= rectangles.Length
                    invariant 0 <= size <= rectangles.Length
                    invariant temp != null
                    invariant rectangles.Length == temp.Length
                    invariant temp[i] != null
                    decreases temp.Length - j;
                {
                    if (temp[j] != null && size > 1)
                    {
                        var b := canMerge(temp[i], temp[j]);

                        if (b)
                        {
                            var r := merge(temp[i], temp[j]);

                            temp[i] := r;
                            temp[j] := null;
                            size := size - 1;
                            rectangles := temp;
                            return;
                        }
                    }

                    j := j + 1;
                }
            }
            i := i + 1;
        }
    }

    /*
     * Fusionne les rectangles de la couverture jusqu'à l'obtention d'une
     * couverture localement optimale.
     */
    method optimize()
        requires ok()
        ensures ok()
        modifies this
    {
        var size := this.size;

        if (this.size > 1)
        {
            improve();
        }

        while (size != this.size && size > 1)
            invariant rectangles != null
            invariant 0 <= this.size <= rectangles.Length
            decreases size
        {
            size := size - 1;

            if (this.size > 1)
            {
                improve();
            }
        }
    }

    /*
     * Le nom dit tout, cela dit la méthode n'est pas utilisée, mais bon, c'est
     * une méthode de la phase 1.
     */
    method contains(x: int, y: int)
        returns (b: bool)
        requires ok()
    {
        b := false;

        var i := 0;

        while (i < rectangles.Length && !b)
        {
            if (rectangles[i] != null)
            {
                var rX := rectangles[i].getX();
                var rY := rectangles[i].getY();

                if (x == rX && y == rY)
                {
                    b := true;
                }
            }

            i := i + 1;
        }
    }

    /*
     * Affiche les rectangles de la couverture.
     */
    method dump()
        requires ok()
    {
        print("[ ");

        if (rectangles.Length > 0 && rectangles[0] != null)
        {
            rectangles[0].dump();
        }

        var i := 0;
        while (i < rectangles.Length - 1)
        {
            if (rectangles[i] != null)
            {
                print(", ");
                rectangles[i].dump();
            }
            i := i + 1;
        }

        if (rectangles.Length > 0 && i < rectangles.Length && rectangles[i] != null)
        {
            print(", ");
            rectangles[i].dump();
        }

        print(" ]\n");
    }

    /*
     * Affiche les rectangles de la couverture, mais dans un format différent.
     */
    method customDump()
        requires ok()
    {
        var i := 0;

        while (i < rectangles.Length - 1)
        {
            if (rectangles[i] != null)
            {
                rectangles[i].dump();
            }

            i := i + 1;
        }

        if (i < rectangles.Length && rectangles[i] != null)
        {
            rectangles[i].dump();
        }
    }
}

/*
 * Retourne a si a < b, b sinon.
 */
method min(a: int, b: int)
    returns (c: int)
{
    c := b;

    if (a < b)
    {
        c := a;
    }
}

/*
 * Si r1 et r2 sont distincts et qu'il est possible de les fusionner, alors
 * retourne 'true', sinon 'false'.
 */
method canMerge(r1: Rectangle, r2: Rectangle)
    returns (b: bool)
    requires r1 != null
    requires r2 != null
{
    var r1X := r1.getX();
    var r2X := r2.getX();
    var r1Y := r1.getY();
    var r2Y := r2.getY();
    var r1W := r1.getWidth();
    var r2W := r2.getWidth();
    var r1H := r1.getHeight();
    var r2H := r2.getHeight();

    b := true;

    if r1X == r2X && r1Y == r2Y {b := false;}
    if r1X != r2X && r1Y != r2Y {b := false;}

    if (b)
    {
        if r1X == r2X && r1W != r2W {b := false;}
        if r1Y == r2Y && r1H != r2H {b := false;}
    }
}

/*
 * Retourne la fusion de r1 et r2, on suppose que r1 et r2 peuvent être
 * fusionnés.
 */
method merge(r1: Rectangle, r2: Rectangle)
    returns (r: Rectangle)
    requires r1 != null
    requires r2 != null
    ensures r != null
{
    var r1X := r1.getX();
    var r2X := r2.getX();
    var r1Y := r1.getY();
    var r2Y := r2.getY();
    var r1W := r1.getWidth();
    var r2W := r2.getWidth();
    var r1H := r1.getHeight();
    var r2H := r2.getHeight();

    var rX := min(r1X, r2X);
    var rY := min(r1Y, r2Y);

    var rH := -1;
    var rW := -1;

    if r1X != r2X
    {
        rH := r1H;
        rW := r1W + r2W;
    }
    else
    {
        rW := r1W;
        rH := r1H + r2H;
    }

    r := new Rectangle(rX, rY, rW, rH);
}

method Main()
{
    var rectangles := new Rectangle[3];
    rectangles[0] := new Rectangle(0, 0, 32, 32);
    rectangles[1] := new Rectangle(32, 0, 32, 32);
    rectangles[2] := new Rectangle(64, 64, 64, 32);

    var couverture := new Couverture(rectangles);

    //print("---IN---\n");

    //couverture.dump();

    couverture.optimize();

    //print("---OUT--\n");

    couverture.dump();

    rectangles := new Rectangle[0];
    couverture := new Couverture(rectangles);
    couverture.optimize();
    couverture.dump();

    rectangles := new Rectangle[2];
    rectangles[0] := new Rectangle(0, 0, 32, 32);
    rectangles[1] := new Rectangle(32, 0, 32, 32);
    couverture := new Couverture(rectangles);
    couverture.optimize();
    couverture.dump();
}
