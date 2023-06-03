declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        call void @p()
        ret i32 0
}

define i32 @f() {
    entry:
        br i1 1, label %L0, label %L1
    L0:
        ret i32 0
    L1:
        ret i32 1
}

define i32 @g() {
    entry:
        br i1 0, label %L3, label %L4
    L3:
        br label %L2
    L4:
        ret i32 0
    L2:
        ret i32 1
}

define void @p() {
    entry:
        ret void
}
