/*****************************************************************************

                        Copyright ©

******************************************************************************/

implement game
    inherits formWindow
    open core, vpiDomains, vpi, math, stdio

constants
    className = "game/game".
    classVersion = "".


class facts
    %w:windowHandle:=vpiDomains::nullWindow.
    max_row:integer:=30.
    max_col:integer:=40.
    margin:integer:=20.
    maxDepth:integer:=0.

    cell:(integer Row,integer Col,integer Type).
    edge:(pnt Pnt1,pnt Pnt2).
    parent:(pnt Parent, pnt Child).
    vertex:(pnt Pnt,color Color).
    shoot:(integer I,integer J,integer Direction,boolean IsMoved).

    greyList:pntlist:=[].

    pathList_en1:pntlist:=[].
    pathList_en1_pl1:pntlist:=[].
    pathList_en1_pl2:pntlist:=[].
    pathList_en1_pl1_size:integer:=0.
    pathList_en1_pl2_size:integer:=0.

    pathList_en2:pntlist:=[].
    pathList_en2_pl1:pntlist:=[].
    pathList_en2_pl2:pntlist:=[].
    pathList_en2_pl1_size:integer:=0.
    pathList_en2_pl2_size:integer:=0.

    flag_moved_for_en1:boolean := true.
    flag_moved_for_en2:boolean := true.

    lives_pl1:integer:= 3.
    lives_pl2:integer:= 3.
    lives_en1:integer:= 3.
    lives_en2:integer:= 3.

    is_alive_pl1:boolean := true.
    is_alive_pl2:boolean := true.
    is_alive_en1:boolean := true.
    is_alive_en2:boolean := true.

    tank_color_pl1:color:=color_GreenYellow.
    tank_color_pl2:color:=color_LightGreen.
    tank_color_en1:color:=color_Salmon.
    tank_color_en2:color:=color_VioletRed.





    srcPnt1:pnt:=pnt(0,0).
    srcPnt2:pnt:=pnt(0,0).

    shootPnt:pnt:=pnt(0,0).


    %flag:boolean:=false.

    timer_1:timerId:=erroneous.
    timer_2:timerId:=erroneous.

    timer_fire:timerId:=erroneous.

    %type_color_EMPTY:color:=color_White.
    %type_color_REACHABLE:color:=color_Gray.
    %type_color_EMPTY:color:=color_White.

    type_EMPTY:integer     :=0.
    type_WALL:integer      :=1.
    type_PLAYER_1:integer:=2.
    type_PLAYER_2:integer:=3.
    type_ENEMY_1:integer:=4.
    type_ENEMY_2:integer:=5.

    %flag_moved_for_en1:boolean:=false.
    %flag_moved_for_en1_tank2:boolean:=false.

    tank1:pnt:=pnt(0,0).
    direction1:integer  := 6.

    tank2:pnt:=pnt(0,0).
    direction2:integer  := 6.

    enemy_tank1:pnt:=pnt(0,0).
    enemy_tank1_previous:pnt:=pnt(0,0).
    enemy_direction1:integer  := 4.

    enemy_tank2:pnt:=pnt(0,0).
    enemy_tank2_previous:pnt:=pnt(0,0).
    enemy_direction2:integer  := 4.

class predicates
    showMatrix:(windowHandle W, integer I,integer J).
clauses
    showMatrix(_,I,_):-
        I>=max_row,!.
    showMatrix(W,I,J):-
        J>=max_col,!,
        showMatrix(W,I+1,0).
     showMatrix(W,I,J):-
        cell(I,J,type_WALL),!, % Wall
        winSetBrush(W,brush(2,color_BurlyWood)),
        drawRect(W,rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),
        showMatrix(W,I,J+1).
     showMatrix(W,I,J):-
        cell(I,J,type_EMPTY),!, % empty cell
        winSetBrush(W,brush(0,color_WhiteSmoke)),
        drawRect(W,rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),
        showMatrix(W,I,J+1).
    showMatrix(W,I,J):-
        showMatrix(W,I,J+1).


predicates
    drawEnemyTanks:(windowHandle W).
clauses
    drawEnemyTanks(W):-
        is_alive_en1 = true,
        enemy_tank1 = pnt(I,J),
        drawTank(W,I,J,type_ENEMY_1,enemy_direction1),
        fail.
    drawEnemyTanks(W):-
        is_alive_en2 = true,
        enemy_tank2 = pnt(I1,J1),
        drawTank(W,I1,J1,type_ENEMY_2,enemy_direction2),
        fail.
    drawEnemyTanks(_):-
        succeed().


predicates
    drawPlayerTanks:(windowHandle W).
clauses
    drawPlayerTanks(W):-
        is_alive_pl1 = true,
        tank1 = pnt(I,J),
        drawTank(W,I,J,type_PLAYER_1,direction1),
        fail.
    drawPlayerTanks(W):-
        is_alive_pl2 = true,
        tank2 = pnt(I1,J1),
        drawTank(W,I1,J1,type_PLAYER_2,direction2),
        fail.
    drawPlayerTanks(_):-
        succeed().

predicates
    killEnemy:(integer Type).
clauses
    killEnemy(type_ENEMY_1):-
        lives_en1 := lives_en1 - 1,
            Lives = lives_en1, writef("% ",Lives),
        lives_en1 = 0,
        is_alive_en1 := false,
        vpi::timerKill(timer_1),
        enemy_tank1 = pnt(I,J),
        retract(cell(I,J,type_ENEMY_1)),
        assert(cell(I,J,type_EMPTY)),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),
        checkGameOver(type_ENEMY_1),
        fail.
    killEnemy(type_ENEMY_2):-
        lives_en2 := lives_en2 - 1,
            Lives = lives_en2, writef("% ",Lives),
        lives_en2 = 0,
        is_alive_en2 := false,
        vpi::timerKill(timer_2),
        enemy_tank2 = pnt(I,J),
        retract(cell(I,J,type_ENEMY_2)),
        assert(cell(I,J,type_EMPTY)),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),
        checkGameOver(type_ENEMY_2),
        fail.
    killEnemy(_):-
        invalidate(rct(margin ,margin+ 10 + max_row*10, margin + max_col*10 ,margin + max_col*10)),
        succeed().

predicates
    killPlayer:(integer Type).
clauses
    killPlayer(type_PLAYER_1):-
        lives_pl1 := lives_pl1 - 1,
            Lives = lives_pl1, writef("% ",Lives),
        lives_pl1 = 0,
        is_alive_pl1 := false,
        flag_moved_for_en1 := true,
        flag_moved_for_en2 := true,
        tank1 = pnt(I,J),
        retract(cell(I,J,type_PLAYER_1)),
        assert(cell(I,J,type_EMPTY)),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),
        checkGameOver(type_PLAYER_1),
        fail.
    killPlayer(type_PLAYER_2):-
        lives_pl2 := lives_pl2 - 1,
            Lives = lives_pl2, writef("% ",Lives),
        lives_pl2 = 0,
        is_alive_pl2 := false,
        flag_moved_for_en1 := true,
        flag_moved_for_en2 := true,
        tank2 = pnt(I,J),
        retract(cell(I,J,type_PLAYER_2)),
        assert(cell(I,J,type_EMPTY)),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),
        checkGameOver(type_PLAYER_2),
        fail.
    killPlayer(_):-
        invalidate(rct(margin ,margin+ 10 + max_row*10, margin + max_col*10 ,margin + max_col*10)),
        succeed().

predicates
    checkGameOver:(integer Type).
clauses
    checkGameOver(type_PLAYER_1):-
        is_alive_pl2 = false,
        vpi::timerKill(timer_fire),
        %popup("you lost!")
        vpiCommonDialogs::note("you lost!"),
        write("you lost!"),
        fail.
    checkGameOver(type_PLAYER_2):-
        is_alive_pl1 = false,
        vpi::timerKill(timer_fire),
        %popup("you lost!")
        vpiCommonDialogs::note("you lost!"),
        write("you lost!"),
        fail.
    checkGameOver(type_ENEMY_1):-
        is_alive_en2 = false,
        vpi::timerKill(timer_fire),
        %popup("you won!")
        vpiCommonDialogs::note("you won!"),
        write("you won!"),
        fail.
    checkGameOver(type_ENEMY_2):-
        is_alive_en1 = false,
        vpi::timerKill(timer_fire),
        %popup("you won!")
        vpiCommonDialogs::note("you won!"),
        write("you won!"),
        fail.
    checkGameOver(_):-
        succeed().

class predicates
    drawTank:(windowHandle W,integer I, integer J, integer Type, integer Direction).
clauses
    drawTank(W,_,_,type_PLAYER_1,_):-
        winSetBrush(W,brush(2,tank_color_pl1)),
        fail.
    drawTank(W,_,_,type_PLAYER_2,_):-
        winSetBrush(W,brush(2,tank_color_pl2)),
        fail.
    drawTank(W,_,_,type_ENEMY_1,_):-
        winSetBrush(W,brush(2,tank_color_en1)),
        fail.
    drawTank(W,_,_,type_ENEMY_2,_):-
        winSetBrush(W,brush(2,tank_color_en2)),
        fail.
    drawTank(W,I,J,_,_):-
        drawRect(W,rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),
        drawEllipse(W,rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),
        fail.
    drawTank(W,I,J,_,4):-
        drawLine(W,pnt(5+margin+J*10,5+margin+I*10),pnt(5+margin+J*10-10,5+margin+I*10)),
        fail.
    drawTank(W,I,J,_,6):-
        drawLine(W,pnt(5+margin+J*10,5+margin+I*10),pnt(5+margin+J*10+10,5+margin+I*10)),
        fail.
    drawTank(W,I,J,_,2):-
        drawLine(W,pnt(5+margin+J*10,5+margin+I*10),pnt(5+margin+J*10,5+margin+I*10+10)),
        fail.
    drawTank(W,I,J,_,8):-
        drawLine(W,pnt(5+margin+J*10,5+margin+I*10),pnt(5+margin+J*10,5+margin+I*10-10)),
        fail.
    drawTank(_,_,_,_,_).

%class predicates
%    showEdges:(windowHandle W) procedure(i).
%clauses
%    showEdges(_):-
%        %edge(pnt(I1,J1),pnt(I2,J2)),
%        %drawLine(W,pnt(margin+J1*10+5,margin+I1*10+5), pnt(margin+J2*10+5,margin+I2*10+5)).
%        vertex(Point,color_Gray),
%        pnt(I,J) = Point,
%        winSetBrush(W,brush(2,color_Yellow)),
%        drawRect(W,rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),
%        fail.
%    showEdges(W):-
%        vertex(Point,color_Red),
%        pnt(I,J) = Point,
%        winSetBrush(W,brush(2,color_Red)),
%        drawRect(W,rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),
%        fail.
%    showEdges(W):-
%        vertex(Point,color_Olive),
%        pnt(I,J) = Point,
%        winSetBrush(W,brush(2,tank_color_pl1)),
%        drawRect(W,rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),
%        fail.
%    showEdges(_).

class predicates
    setSpaces:(integer I, integer J).
clauses
    setSpaces(max_row,_):- !.
    setSpaces(I,max_col):-!,
        setSpaces(I+1,0).
    setSpaces(I,J):-
       assert(cell(I,J,type_EMPTY)),  % type_EMPTY
       setSpaces(I,J+1).

class predicates
    setVWall:(integer Quantity) determ.
clauses
    setVWall(0):- !.
    setVWall(Q):-
     % vertical
      WX = random(max_col),
      WY = 1+random(max_row-2),
      retract(cell(WY,WX,_)),!, assert(cell(WY,WX,type_WALL)),
      retract(cell(WY-1,WX,_)),!, assert(cell(WY-1,WX,type_WALL)),
      retract(cell(WY+1,WX,_)),!, assert(cell(WY+1,WX,type_WALL)),
      setVWall(Q-1).

class predicates
    setHWall:(integer Quantity) determ.
clauses
    setHWall(0):- !.
     setHWall(Q):- % horizintal
        WX =1+ random(max_col-2),
        WY = random(max_row),
        retract(cell(WY,WX,_)),!, assert(cell(WY,WX,type_WALL)),
        retract(cell(WY,WX-1,_)),!,  assert(cell(WY,WX-1,type_WALL)),
        retract(cell(WY,WX+1,_)),!,  assert(cell(WY,WX+1,type_WALL)),
        setHWall(Q-1).

class predicates
    setupGraph:(integer I,integer J) nondeterm.
clauses
    setupGraph(I,_):-
        I>=max_row,!.
     setupGraph(I,J):-
        J>=max_col,!,
        setupGraph(I+1,0).
     setupGraph(I,J):-
        cell(I,J,Type),
        Type = type_WALL,!, % wall
        setupGraph(I,J+1).
    setupGraph(I,J):- % this is not wall
        % check right
        I<max_row,
        J<max_col,

        assert(vertex(pnt(I,J),color_Black)),

        cell(I,J+1,type_EMPTY),
        assert(edge(pnt(I,J),pnt(I,J+1))),
        assert(edge(pnt(I,J+1),pnt(I,J))),
        fail.
    setupGraph(I,J):- % this is not wall
        % check down
        I<max_row,
        J<max_col,
        cell(I+1,J,type_EMPTY),
        assert(edge(pnt(I,J),pnt(I+1,J))),
        assert(edge(pnt(I+1,J),pnt(I,J))),
        fail.
     setupGraph(I,J):- % this is not wall
        setupGraph(I,J+1).





class predicates
   setupField:().
clauses
   setupField():-
        setSpaces(0,0),
        setVWall(50),
        setHWall(50),
        setupGraph(0,0),
        addTank(type_PLAYER_1), % player's tank
        addTank(type_PLAYER_2), % player's tank
        addTank(type_ENEMY_1), % AI's tank
        addTank(type_ENEMY_2), % AI's tank

        fail.
   setupField():-!.



class predicates
   addTank:(integer TankType) nondeterm.
clauses
   addTank(type_PLAYER_1):- % player's tank
        RandRow = random(max_row),
        RandCol = random(max_col div 2),
        cell(RandRow,RandCol,0),!,
            assert(cell(RandRow,RandCol,type_PLAYER_1)),
            tank1 := pnt(RandRow,RandCol).
    addTank(type_PLAYER_2):- % player's tank
        RandRow = random(max_row),
        RandCol = random(max_col div 2),
        cell(RandRow,RandCol,0),!,
            assert(cell(RandRow,RandCol,type_PLAYER_2)),
            tank2 := pnt(RandRow,RandCol).
    addTank(type_ENEMY_1):- % AI's tank
        RandRow = random(max_row),
        RandCol = max_col div 2 + random(max_col div 2),
        cell(RandRow,RandCol,0),!,
            assert(cell(RandRow,RandCol,type_ENEMY_1)),
            enemy_tank1 := pnt(RandRow,RandCol).
    addTank(type_ENEMY_2):- % AI's tank
        RandRow = random(max_row),
        RandCol = max_col div 2 + random(max_col div 2),
        cell(RandRow,RandCol,0),!,
            assert(cell(RandRow,RandCol,type_ENEMY_2)),
            enemy_tank2 := pnt(RandRow,RandCol).
    addTank(TankType):-
        addTank(TankType).
% -----------------------------------------------------------------------------



clauses
    classInfo(className, classVersion).
clauses
    display(Parent) = Form :-
        Form = new(Parent),
        Form:show().
 clauses
    new(Parent):-
        formWindow::new(Parent),
        generatedInitialize().

predicates
    onPaint : drawWindow::paintResponder.
clauses
    onPaint(_Source, _Rectangle, _GDI):-
        W=getVpiWindow(),

        winSetBrush(W,brush(2,color_GrayE0)),
        drawRect(W,rct(margin,margin,margin+max_col*10,margin+max_row*10)), % backround of the playground
        showMatrix(W,0,0),% all spaces and walls
        %showEdges(W),

        drawEnemyTanks(W),
        drawPlayerTanks(W),

        drawAllShoots(W),

        drawLives(W),

        fail.
    onPaint(_Source, _Rectangle, _GDI).

predicates
    drawLives:(windowHandle W).
clauses
    drawLives(W):-


        winSetBrush(W,brush(2,color_White)),
        drawRect(W,rct(margin ,margin+ 10 + max_row*10, margin + max_col*10 ,margin + max_col*10)),


        winSetBrush(W,brush(2,tank_color_pl1)),
        drawTankLives(W,0,0,lives_pl1),

        winSetBrush(W,brush(2,tank_color_pl2)),
        drawTankLives(W,1,0,lives_pl2),

        winSetBrush(W,brush(2,tank_color_en1)),
        drawTankLives(W,0,1,lives_en1),

        winSetBrush(W,brush(2,tank_color_en2)),
        drawTankLives(W,1,1,lives_en2),

        succeed().

predicates
    drawTankLives:(windowHandle W,integer I,integer J,integer LeftLives).
clauses
    drawTankLives(_,_,_,0):-!.
    drawTankLives(W,I,J,LeftLives):-
        RadiosMult2 = 20,
        Top = margin*2 + max_row*10 + I* 50,
        Left = (1-J)*margin + max_col*10*J + LeftLives*15*(1-2*J) ,
        T=Top,
        L=Left,
        B=T+RadiosMult2,
        R=L+RadiosMult2,
        drawEllipse(W,rct(L,T,R,B)),
        drawTankLives(W,I,J,LeftLives-1).



predicates
    reset4bfs:().
clauses
    reset4bfs():-
        vertex(Point,color_Olive),
        retract(vertex(Point,color_Olive)),
        assert(vertex(Point,color_Black)),
        fail.
    reset4bfs():-
        vertex(Point,color_Red),
        retract(vertex(Point,color_Red)),
        assert(vertex(Point,color_Black)),
        fail.
    reset4bfs().


predicates
    bfs:() procedure.
clauses
    bfs():-
        greyList = [H|T],
        greyList := T,

        retract(vertex(H,color_Gray)),% gray -> seen
        assert(vertex(H,color_Red)),  % red -> visited

%            H = pnt(I,J),
%            invalidate(rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),

        edge(H,N),                               % N = H.getNeighbor()
        retract(vertex(N,color_Black)),
        assert(vertex(N,color_Gray)),
        assert(parent(H,N)),                  % N.setParent(H)

        concat(greyList,[N],TmpList),
        greyList := TmpList,

%            N = pnt(I,J),
%            invalidate(rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),
        fail.
    bfs().



predicates
    first:() procedure.
clauses
    first():-
        maxDepth<>0,
        %writef("maxDepth=%\n",maxDepth),
        bfs(),
        maxDepth := maxDepth-1,
        first(),
        fail.
    first().

predicates
    head:(pnt Start) procedure.
clauses
    head(Start):-
        retractAll(parent(_,_)),
        reset4bfs(),
        retract(vertex(Start,color_Black)),% black -> unseen
        assert(vertex(Start,color_Gray)),% gray -> seen
        maxDepth := max_row*max_col,
        greyList := [Start],% queue of seen pnt's
        first(),
        fail.
    head(_).



predicates
    onTimer : window::timerListener.
clauses
    onTimer(_Source, timer_1):-
        flag_moved_for_en1 = true,
        srcPnt1 := enemy_tank1,
        pathList_en1_pl1 := [],
        pathList_en1_pl2 := [],
        pathList_en1_pl1_size := max_col*max_row,
        pathList_en1_pl2_size := max_col*max_row,
        head(srcPnt1),% builds the bfs tree
            writef("\t 1-- srcPnt1=% ---> tank1=%\n",enemy_tank1,tank1),
            writef("\t 1-- srcPnt1=% ---> tank2=%\n",enemy_tank1,tank2),
        fail.

    onTimer(_Source, timer_1):-
        flag_moved_for_en1 = true,
        is_alive_pl1=true,
        findPath(type_ENEMY_1,type_PLAYER_1,tank1),
            writef("pathList_en1_pl1=%\n",pathList_en1_pl1),
        fail.
    onTimer(_Source, timer_1):-
        flag_moved_for_en1 = true,
        is_alive_pl2=true,
        findPath(type_ENEMY_1,type_PLAYER_2,tank2),
            writef("pathList_en1_pl2=%\n",pathList_en1_pl2),
        fail.
    onTimer(_Source, timer_1):-
        pathList_en1_pl1_size < pathList_en1_pl2_size,
        flag_moved_for_en1 = true,
        pathList_en1 := pathList_en1_pl1,
        fail.
    onTimer(_Source, timer_1):-
        pathList_en1_pl1_size >= pathList_en1_pl2_size,
        flag_moved_for_en1 = true,
        pathList_en1 := pathList_en1_pl2,
        fail.
    onTimer(_Source, timer_1):-
        flag_moved_for_en1 := false,
        moveTank(type_ENEMY_1),
        %oliveToBlack(),
        enemy_tank1 = pnt(I,J),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),
        fail.

    onTimer(_Source, timer_1):-
        enemyShoots(type_ENEMY_1),
        fail.

        % enemy 2---------------------------------------------------------------

    onTimer(_Source, timer_2):-
        %writef("timer:%",2),
        %retractAll(parent(_,_)),
        flag_moved_for_en2 = true,
        srcPnt2 := enemy_tank2,
        pathList_en2_pl1 := [],
        pathList_en2_pl2 := [],
        pathList_en2_pl1_size := max_col*max_row,
        pathList_en2_pl2_size := max_col*max_row,
        head(srcPnt2),% builds the bfs tree
            writef("\t 2-- srcPnt2=% ---> tank1=%\n",enemy_tank2,tank1),
            writef("\t 2-- srcPnt2=% ---> tank2=%\n",enemy_tank2,tank2),
        fail.

    onTimer(_Source, timer_2):-
        flag_moved_for_en2 = true,
        is_alive_pl1=true,
        findPath(type_ENEMY_2,type_PLAYER_1,tank1),
            writef("pathList_en2_pl1=%\n",pathList_en2_pl1),
        fail.
    onTimer(_Source, timer_2):-
        flag_moved_for_en2 = true,
        is_alive_pl2=true,
        findPath(type_ENEMY_2,type_PLAYER_2,tank2),
            writef("pathList_en2_pl2=%\n",pathList_en2_pl2),
        fail.

    onTimer(_Source, timer_2):-
        pathList_en2_pl1_size < pathList_en2_pl2_size,
        flag_moved_for_en2 = true,
        pathList_en2 := pathList_en2_pl1,
        fail.
    onTimer(_Source, timer_2):-
        pathList_en2_pl1_size >= pathList_en2_pl2_size,
        flag_moved_for_en2 = true,
        pathList_en2 := pathList_en2_pl2,
        fail.
    onTimer(_Source, timer_2):-
        flag_moved_for_en2 := false,
        moveTank(type_ENEMY_2),
        %oliveToBlack(),
        enemy_tank2 = pnt(I,J),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),
        fail.
    onTimer(_Source, timer_2):-
        enemyShoots(type_ENEMY_2),
        fail.

    onTimer(_Source, timer_fire):-
        moveAllShoots(),
        fail.
    onTimer(_Source, _TimerId).






predicates
    enemyShoots:(integer Type).
clauses
    enemyShoots(type_ENEMY_1):-
        findShootReason(enemy_tank1,pathList_en1,0),
        pnt(I1,J1) = enemy_tank1,
        pathList_en1 = [H|_],
        pnt(I2,J2) = H,
        changeCannon(I1,J1,I2,J2,type_ENEMY_1),
        invalidate(rct(margin+(J1-1)*10,margin+(I1-1)*10,margin+(J1+2)*10,margin+(I1+2)*10)),
        assert(shoot(I1,J1,enemy_direction1,false)),
        fail.
    enemyShoots(type_ENEMY_2):-
        findShootReason(enemy_tank2,pathList_en2,0),
        pnt(I1,J1) = enemy_tank2,
        pathList_en2 = [H|_],
        pnt(I2,J2) = H,
        changeCannon(I1,J1,I2,J2,type_ENEMY_2),
        invalidate(rct(margin+(J1-1)*10,margin+(I1-1)*10,margin+(J1+2)*10,margin+(I1+2)*10)),
        assert(shoot(I1,J1,enemy_direction2,false)),
        fail.
    enemyShoots(_).

predicates
    changeCannon:(integer I1,integer J1,integer I2,integer J2, integer Type).
clauses
    changeCannon(I1,J1,I2,J2,type_ENEMY_1):-
    I1 = I2,
    J1 > J2,
    enemy_direction1 := 4,
    fail.
    changeCannon(I1,J1,I2,J2,type_ENEMY_1):-
    I1 = I2,
    J1 < J2,
    enemy_direction1 := 6,
    fail.
    changeCannon(I1,J1,I2,J2,type_ENEMY_1):-
    I1 > I2,
    J1 = J2,
    enemy_direction1 := 8,
    fail.
    changeCannon(I1,J1,I2,J2,type_ENEMY_1):-
    I1 < I2,
    J1 = J2,
    enemy_direction1 := 2,
    fail.
    changeCannon(I1,J1,I2,J2,type_ENEMY_2):-
    I1 = I2,
    J1 > J2,
    enemy_direction2 := 4,
    fail.
    changeCannon(I1,J1,I2,J2,type_ENEMY_2):-
    I1 = I2,
    J1 < J2,
    enemy_direction2 := 6,
    fail.
    changeCannon(I1,J1,I2,J2,type_ENEMY_2):-
    I1 > I2,
    J1 = J2,
    enemy_direction2 := 8,
    fail.
    changeCannon(I1,J1,I2,J2,type_ENEMY_2):-
    I1 < I2,
    J1 = J2,
    enemy_direction2 := 2,
    fail.
    changeCannon(_,_,_,_,_).

predicates
    findShootReason:(pnt Src,pntlist L, integer SameDir) nondeterm. % 0->init    1->same_row   2->same_col
clauses
    findShootReason(_,[],1).% last step, same row is kept
    findShootReason(_,[],2).% last step, same col is kept
    findShootReason(Src,L,0):-% only one step -> shoot!
        L <> [],
        L = [H|T],
        Src=pnt(I1,_),
        H=pnt(I2,_),
        I1 = I2,
        findShootReason(H,T,1),

        succeed().
    findShootReason(Src,L,0):-% only one step -> shoot!
        L <> [],
        L = [H|T],
        Src=pnt(_,J1),
        H=pnt(_,J2),
        J1 = J2,
        findShootReason(H,T,2),
        succeed().

    findShootReason(Src,L,1):-
        L = [H|T],
        Src=pnt(I1,_),
        H=pnt(I2,_),
        I1 = I2,
        findShootReason(H,T,1),
        succeed().
    findShootReason(Src,L,2):-
        L = [H|T],
        Src=pnt(_,J1),
        H=pnt(_,J2),
        J1 = J2,
        findShootReason(H,T,2),
        succeed().








predicates
    drawAllShoots:(windowHandle W).
clauses
    drawAllShoots(W):-
        winSetBrush(W,brush(2,color_OrangeRed)),
        shoot(I,J,_,_),
        drawRect(W,rct(margin+J*10+3,margin+I*10+3,margin+J*10+7,margin+I*10+7)),
        fail.
    drawAllShoots(_).

predicates
    moveShoot:(integer I,integer J,integer Dir).
clauses
    moveShoot(I,J,8):-
        shootPnt := pnt(I-1,J),
        fail.
    moveShoot(I,J,2):-
        shootPnt := pnt(I+1,J),
        fail.
    moveShoot(I,J,4):-
        shootPnt := pnt(I,J-1),
        fail.
    moveShoot(I,J,6):-
        shootPnt := pnt(I,J+1),
        fail.

    moveShoot(I,J,Dir):- % EMPTY
        pnt(I1,J1) = shootPnt,
        cell(I1,J1,type_EMPTY),
        retract(shoot(I,J,Dir,false)),
        assert(shoot(I1,J1,Dir,true)),
        fail.
    moveShoot(I,J,Dir):- % type_WALL
        pnt(I1,J1) = shootPnt,
        cell(I1,J1,type_WALL),
        retract(shoot(I,J,Dir,false)),
        %assert(explosion(I1,J1,Dir)),
        fail.

    moveShoot(I,J,Dir):- % type_ENEMY_1
        pnt(I1,J1) = shootPnt,
        cell(I1,J1,type_ENEMY_1),
        retract(shoot(I,J,Dir,_)),
        killEnemy(type_ENEMY_1),
        fail.
    moveShoot(I,J,Dir):- % type_ENEMY_2
        pnt(I1,J1) = shootPnt,
        cell(I1,J1,type_ENEMY_2),
        retract(shoot(I,J,Dir,_)),
        killEnemy(type_ENEMY_2),
        fail.

    moveShoot(I,J,Dir):- % type_PLAYER_1
        pnt(I1,J1) = shootPnt,
        cell(I1,J1,type_PLAYER_1),
        retract(shoot(I,J,Dir,_)),
        killPlayer(type_PLAYER_1),
        fail.
    moveShoot(I,J,Dir):- % type_PLAYER_2
        pnt(I1,J1) = shootPnt,
        cell(I1,J1,type_PLAYER_2),
        retract(shoot(I,J,Dir,_)),
        killPlayer(type_PLAYER_2),
        fail.
    moveShoot(I,J,Dir):- % out of bounds
        shoot(I,J,Dir,_),
        retract(shoot(I,J,Dir,false)),
        %assert(explosion(I1,J1,Dir)),
        fail.

    moveShoot(I,J,8):-
        pnt(I1,J1) = shootPnt,
        invalidate(rct(margin+(J+1)*10,margin+(I+1)*10,margin+(J1)*10,margin+(I1)*10)),
        fail.
    moveShoot(I,J,2):-
        pnt(I1,J1) = shootPnt,
        invalidate(rct(margin+(J)*10,margin+(I)*10,margin+(J1+1)*10,margin+(I1+1)*10)),
        fail.
    moveShoot(I,J,4):-
        pnt(I1,J1) = shootPnt,
        invalidate(rct(margin+(J+1)*10,margin+(I+1)*10,margin+(J1)*10,margin+(I1)*10)),
        fail.
    moveShoot(I,J,6):-
        pnt(I1,J1) = shootPnt,
        invalidate(rct(margin+(J)*10,margin+(I)*10,margin+(J1+1)*10,margin+(I1+1)*10)),
        fail.
    moveShoot(_,_,_).

predicates
    moveAllShoots:() procedure.
clauses
    moveAllShoots():-
        shoot(I,J,Dir,false),
        moveShoot(I,J,Dir),
        fail.
    moveAllShoots():-
        retract(shoot(I,J,Dir,true)),
        assert(shoot(I,J,Dir,false)),
        fail.
    moveAllShoots().

class predicates
    concat:(pntList L1, pntList L2,pntList L3) procedure (i,i,o).
clauses
    concat([],L2,L2).
    concat([H|T],L2,[H|TmpList]):-
        concat(T,L2,TmpList).

/*
init:
    all -> black.

 if flag_moved_for_en1=true{
 all -> black
head:
    all kashir -> red
    rest -> black
findpath
    all path -> olive
    all kashir not path -> red
    rest -> black
 if flag_moved_for_en1=false,
}
move:: onTimer
    every step:
        newpnt -> red


*/

%predicates
%    oliveToBlack:()procedure.
%clauses
%    oliveToBlack():-
%        pathList_en1_pl1 = [H|T],
%        pathList_en1_pl1 := T,
%        retract(vertex(H,color_Olive)),
%        assert(vertex(H,color_Red)),
%        oliveToBlack(),
%        fail.
%    oliveToBlack().

% finds the path from enemy# to player#
predicates
    findPath:(integer EnemyType, integer PlayerType, pnt Point) procedure.
clauses
    findPath(type_ENEMY_1,type_PLAYER_1,srcPnt1):-
        pathList_en1_pl1_size := 0,!. % found!
    findPath(type_ENEMY_1,type_PLAYER_2,srcPnt1):-
        pathList_en1_pl2_size := 0,!. % found!
    findPath(type_ENEMY_1,type_PLAYER_1,Point):-
        parent(Parent,Point),
        vertex(Point,color_Red),
%        retract(vertex(Point,color_Red)),% red -> visited
%        assert(vertex(Point,color_Olive)),% olive -> in path

        findPath(type_ENEMY_1,type_PLAYER_1,Parent),

        pathList_en1_pl1_size := pathList_en1_pl1_size + 1,
        concat(pathList_en1_pl1,[Point],TmpList),

%            Point = pnt(I,J),
%            invalidate(rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),

        pathList_en1_pl1:=TmpList,
        fail.
    findPath(type_ENEMY_1,type_PLAYER_2,Point):-
        parent(Parent,Point),
        vertex(Point,color_Red),
%        retract(vertex(Point,color_Red)),% red -> visited
%        assert(vertex(Point,color_Olive)),% olive -> in path

        findPath(type_ENEMY_1,type_PLAYER_2,Parent),

        pathList_en1_pl2_size := pathList_en1_pl2_size + 1,
        concat(pathList_en1_pl2,[Point],TmpList),

%            Point = pnt(I,J),
%            invalidate(rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),

        pathList_en1_pl2:=TmpList,
        fail.

    % enemy 2 ------------------------------------------------------------

    findPath(type_ENEMY_2,type_PLAYER_1,srcPnt2):-
        pathList_en2_pl1_size := 0,!. % found!
    findPath(type_ENEMY_2,type_PLAYER_2,srcPnt2):-
        pathList_en2_pl2_size := 0,!. % found!
    findPath(type_ENEMY_2,type_PLAYER_1,Point):-
        parent(Parent,Point),
        vertex(Point,color_Red),
%        retract(vertex(Point,color_Red)),% red -> visited
%        assert(vertex(Point,color_Olive)),% olive -> in path

        findPath(type_ENEMY_2,type_PLAYER_1,Parent),

        pathList_en2_pl1_size := pathList_en2_pl1_size + 1,
        concat(pathList_en2_pl1,[Point],TmpList),

%            Point = pnt(I,J),
%            invalidate(rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),

        pathList_en2_pl1:=TmpList,
        fail.
    findPath(type_ENEMY_2,type_PLAYER_2,Point):-
        parent(Parent,Point),
        vertex(Point,color_Red),
%        retract(vertex(Point,color_Red)),% red -> visited
%        assert(vertex(Point,color_Olive)),% olive -> in path

        findPath(type_ENEMY_2,type_PLAYER_2,Parent),

        pathList_en2_pl2_size := pathList_en2_pl2_size + 1,
        concat(pathList_en2_pl2,[Point],TmpList),

%            Point = pnt(I,J),
%            invalidate(rct(margin+J*10,margin+I*10,margin+(J+1)*10,margin+(I+1)*10)),

        pathList_en2_pl2:=TmpList,
        fail.

    findPath(_,_,_).


predicates
    moveTank:(integer Type).
clauses
    moveTank(type_ENEMY_1):-% enemy_tank1  ---------
        pathList_en1 = [H|T],
        pathList_en1 := T,

        enemy_tank1_previous := enemy_tank1,
        enemy_tank1 := H,
        fail.
    moveTank(type_ENEMY_1):-
        enemy_tank1 = tank1,
        lives_pl1 := 1,
        killPlayer(type_PLAYER_1),
        fail.
    moveTank(type_ENEMY_1):-
        enemy_tank1 = tank2,
        lives_pl2 := 1,
        killPlayer(type_PLAYER_2),
        fail.
    moveTank(type_ENEMY_1):-
        pnt(TI,TJ)=enemy_tank1_previous,
        retract(cell(TI,TJ,type_ENEMY_1)),
        assert(cell(TI,TJ,type_EMPTY)),

        pnt(TI1,TJ1)=enemy_tank1,
        retract(cell(TI1,TJ1,type_EMPTY)),
        assert(cell(TI1,TJ1,type_ENEMY_1)),
        fail.

    moveTank(type_ENEMY_1):-% enemy_tank1  ---------
        enemy_tank1_previous = pnt(TI,_),
        enemy_tank1 = pnt(TI1,_),
        TI<TI1,
        enemy_direction1 := 2,
        fail.
    moveTank(type_ENEMY_1):-% enemy_tank1  ---------
        enemy_tank1_previous = pnt(TI,_),
        enemy_tank1 = pnt(TI1,_),
        TI>TI1,
        enemy_direction1 := 8,
        fail.
    moveTank(type_ENEMY_1):-% enemy_tank1  ---------
        enemy_tank1_previous = pnt(_,TJ),
        enemy_tank1 = pnt(_,TJ1),
        TJ<TJ1,
        enemy_direction1 := 6,
        fail.
    moveTank(type_ENEMY_1):-% enemy_tank1  ---------
        enemy_tank1_previous = pnt(_,TJ),
        enemy_tank1 = pnt(_,TJ1),
        TJ>TJ1,
        enemy_direction1 := 4,
        fail.



    % enemy 2   -------------------------------------------------------



    moveTank(type_ENEMY_2):-% enemy_tank2  ---------
        pathList_en2 = [H|T],
        pathList_en2 := T,

        enemy_tank2_previous := enemy_tank2,
        enemy_tank2 := H,
        fail.
    moveTank(type_ENEMY_2):-
        enemy_tank2 = tank1,
        lives_pl1 := 1,
        killPlayer(type_PLAYER_1),
        fail.
    moveTank(type_ENEMY_2):-
        enemy_tank2 = tank2,
        lives_pl2 := 1,
        killPlayer(type_PLAYER_2),
        fail.
    moveTank(type_ENEMY_2):-
        pnt(TI,TJ)=enemy_tank2_previous,
        retract(cell(TI,TJ,type_ENEMY_2)),
        assert(cell(TI,TJ,type_EMPTY)),

        pnt(TI1,TJ1)=enemy_tank2,
        retract(cell(TI1,TJ1,type_EMPTY)),
        assert(cell(TI1,TJ1,type_ENEMY_2)),
        fail.

    moveTank(type_ENEMY_2):-% enemy_tank2  ---------
        enemy_tank2_previous = pnt(TI,_),
        enemy_tank2 = pnt(TI2,_),
        TI<TI2,
        enemy_direction2 := 2,
        fail.
    moveTank(type_ENEMY_2):-% enemy_tank2  ---------
        enemy_tank2_previous = pnt(TI,_),
        enemy_tank2 = pnt(TI2,_),
        TI>TI2,
        enemy_direction2 := 8,
        fail.
    moveTank(type_ENEMY_2):-% enemy_tank2  ---------
        enemy_tank2_previous = pnt(_,TJ),
        enemy_tank2 = pnt(_,TJ2),
        TJ<TJ2,
        enemy_direction2 := 6,
        fail.
    moveTank(type_ENEMY_2):-% enemy_tank2  ---------
        enemy_tank2_previous = pnt(_,TJ),
        enemy_tank2 = pnt(_,TJ2),
        TJ>TJ2,
        enemy_direction2 := 4,
        fail.

    moveTank(_):-
        succeed().



predicates
    onKeyDown : drawWindow::keyDownResponder.
clauses
    % ---- player 1
    onKeyDown(_Source, Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling():-
        writef("%\n",Key),
        %Key = 65, % left  A
        Key =100, % left  Arrow
        W=getVpiWindow(),
        tank1 = pnt(I,J),
        % check begin
        edge(pnt(I,J),pnt(I,J-1)),
        % check end
        %flag_moved_for_en1:=true,
        retract(cell(I,J,type_PLAYER_1)),
        assert(cell(I,J,type_EMPTY)),
        tank1 := pnt(I,J-1),
        direction1 := 4, % 4 - left
        retract(cell(I,J-1,type_EMPTY)),
        assert(cell(I,J-1,type_PLAYER_1)),

        drawTank(W,I,J-1,type_PLAYER_1,direction1),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),

        fail.
    onKeyDown(_Source, Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling:-
        %Key = 68, %right D
        Key = 102, % right arrow
        W=getVpiWindow(),
        tank1 = pnt(I,J),
        % check begin
        edge(pnt(I,J),pnt(I,J+1)),
        % check end
        %flag_moved_for_en1:=true,
        retract(cell(I,J,type_PLAYER_1)),
        assert(cell(I,J,type_EMPTY)),
        tank1 := pnt(I,J+1),
        direction1 := 6, % 6 - right
        retract(cell(I,J+1,type_EMPTY)),
        assert(cell(I,J+1,type_PLAYER_1)),

        drawTank(W,I,J+1,type_PLAYER_1,direction1),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),

        fail.
    onKeyDown(_Source, Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling:-
        %Key = 87, % up W
        Key = 104, % up arrow
        W=getVpiWindow(),
        tank1 = pnt(I,J),
        % check begin
        edge(pnt(I,J),pnt(I-1,J)),
        % check end
        %flag_moved_for_en1:=true,
        retract(cell(I,J,type_PLAYER_1)),
        assert(cell(I,J,type_EMPTY)),
        tank1 := pnt(I-1,J),
        direction1 := 8, % 8 - up
        retract(cell(I-1,J,type_EMPTY)),
        assert(cell(I-1,J,type_PLAYER_1)),

        drawTank(W,I-1,J,type_PLAYER_1,direction1),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),

        fail.
    onKeyDown(_Source, Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling:-
        %Key = 83, % down S
        Key = 98, % down arrow
        W=getVpiWindow(),
        tank1 = pnt(I,J),
        % check begin
        edge(pnt(I,J),pnt(I+1,J)),
        % check end
        %flag_moved_for_en1:=true,
        retract(cell(I,J,type_PLAYER_1)),
        assert(cell(I,J,type_EMPTY)),
        tank1 := pnt(I+1,J),
        direction1 := 2, % 2- down
        retract(cell(I+1,J,type_EMPTY)),
        assert(cell(I+1,J,type_PLAYER_1)),

        drawTank(W,I+1,J,type_PLAYER_1,direction1),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),

        fail.


    % ---- player 2
    onKeyDown(_Source, Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling():-
        writef("%\n",Key),
        Key = 65, % left  A
        %Key =100, % left  Arrow
        W=getVpiWindow(),
        tank2 = pnt(I,J),
        % check begin
        edge(pnt(I,J),pnt(I,J-1)),
        % check end
        %flag_moved_for_en1_tank2:=true,
        retract(cell(I,J,type_PLAYER_2)),
        assert(cell(I,J,type_EMPTY)),
        tank2 := pnt(I,J-1),
        direction2 := 4, % 4 - left
        retract(cell(I,J-1,type_EMPTY)),
        assert(cell(I,J-1,type_PLAYER_2)),

        drawTank(W,I,J-1,type_PLAYER_2,direction2),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),

        fail.
    onKeyDown(_Source, Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling:-
        Key = 68, %right D
        %Key = 102, % right arrow
        W=getVpiWindow(),
        tank2 = pnt(I,J),
        % check begin
        edge(pnt(I,J),pnt(I,J+1)),
        % check end
        %flag_moved_for_en1_tank2:=true,
        retract(cell(I,J,type_PLAYER_2)),
        assert(cell(I,J,type_EMPTY)),
        tank2 := pnt(I,J+1),
        direction2 := 6, % 6 - right
        retract(cell(I,J+1,type_EMPTY)),
        assert(cell(I,J+1,type_PLAYER_2)),

        drawTank(W,I,J+1,type_PLAYER_2,direction2),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),

        fail.
    onKeyDown(_Source, Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling:-
        Key = 87, % up W
        %Key = 104, % up arrow
        W=getVpiWindow(),
        tank2 = pnt(I,J),
        % check begin
        edge(pnt(I,J),pnt(I-1,J)),
        % check end
        %flag_moved_for_en1_tank2:=true,
        retract(cell(I,J,type_PLAYER_2)),
        assert(cell(I,J,type_EMPTY)),
        tank2 := pnt(I-1,J),
        direction2 := 8, % 8 - up
        retract(cell(I-1,J,type_EMPTY)),
        assert(cell(I-1,J,type_PLAYER_2)),

        drawTank(W,I-1,J,type_PLAYER_2,direction2),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),

        fail.
    onKeyDown(_Source, Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling:-
        Key = 83, % down S
        %Key = 98, % down arrow
        W=getVpiWindow(),
        tank2 = pnt(I,J),
        % check begin
        edge(pnt(I,J),pnt(I+1,J)),
        % check end
        %flag_moved_for_en1_tank2:=true,
        retract(cell(I,J,type_PLAYER_2)),
        assert(cell(I,J,type_EMPTY)),
        tank2 := pnt(I+1,J),
        direction2 := 2, % 2- down
        retract(cell(I+1,J,type_EMPTY)),
        assert(cell(I+1,J,type_PLAYER_2)),

        drawTank(W,I+1,J,type_PLAYER_2,direction2),
        invalidate(rct(margin+(J-1)*10,margin+(I-1)*10,margin+(J+2)*10,margin+(I+2)*10)),

        fail.

    onKeyDown(_Source, Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling:-
    % need to chack if this not a shoot
        Key<>96, % keypad_0
        Key<>88, % x
        flag_moved_for_en1 := true,
        flag_moved_for_en2 := true,
        fail.

    % if you want to shoot - shoot, don't talk!
    onKeyDown(_Source, 96, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling:-
        is_alive_pl1=true,
        pnt(I,J) = tank1,
        assert(shoot(I,J,direction1,false)),
        fail.
    % if you want to shoot - shoot, don't talk!
    onKeyDown(_Source, 88, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling:-
        is_alive_pl2=true,
        pnt(I,J) = tank2,
        assert(shoot(I,J,direction2,false)),
        fail.

   onKeyDown(_Source, _Key, _ShiftControlAlt) = drawWindow::defaultKeyDownHandling.




predicates
    initAll:(). % start everything
clauses
    initAll():-
        W=getVpiwindow(),
        setupField(),
        invalidate(),
        timer_1 := timerSet(W,650),
        timer_2 := timerSet(W,450),
        timer_fire := timerSet(W,200),
        succeed().

predicates
    onShow : window::showListener.
clauses
    onShow(_Source, _Data):-
        initAll().

% This code is maintained automatically, do not update it manually. 14:32:13-18.4.2013
predicates
    generatedInitialize : ().
clauses
    generatedInitialize():-
        setFont(vpi::fontCreateByName("Tahoma", 8)),
        setText("game"),
        setRect(rct(50,40,400, 400)),
        setDecoration(titlebar([closebutton(),maximizebutton(),minimizebutton()])),
        setBorder(sizeBorder()),
        setState([wsf_ClipSiblings,wsf_ClipChildren]),
        menuSet(noMenu),
        addShowListener(onShow),
        addTimerListener(onTimer),
        setKeyDownResponder(onKeyDown),
        setPaintResponder(onPaint).
% end of automatic code
end implement game
