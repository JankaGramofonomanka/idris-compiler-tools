declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
                                                                                                    ;x = 0
                                                                                                    ;x ~ 0
                                                                                                    ;y = 0
                                                                                                    ;y ~ 0
                                                                                                    ;x = 45
                                                                                                    ;x ~ 45
        %r0 = sub i32 0, 36
                                                                                                    ;y = -(36)
                                                                                                    ;y ~ %r0
        call void @printInt(i32 45)
        call void @printInt(i32 %r0)
        ret i32 0
}
