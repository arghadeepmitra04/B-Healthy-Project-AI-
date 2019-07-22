%%%%%%%%%% Rule Based Expert System Shell %%%%%%%%%%
%%%
%%% This is the expert system with the example from the textbook:
%%%
%%% Artificial Intelligence: 
%%% Structures and strategies for complex problem solving
%%%
%%% by George F. Luger and William A. Stubblefield
%%% 
%%% These programs are copyrighted by Benjamin//Cummings Publishers.
%%%
%%% Modified by Shaun-inn Wu
%%%
%%% These program are offered for educational purposes only.
%%%
%%% Disclaimer: These programs are provided with no warranty whatsoever as to
%%% their correctness, reliability, or any other property.  We have written 
%%% them for specific educational purposes, and have made no effort
%%% to produce commercial quality computer programs.  Please do not expect 
%%% more of them then we have intended.
%%%
%%% This code has been tested with SWI-Prolog (Multi-threaded, Version 7.6.4)
%%% and appears to function as intended.


% solve(Goal): solve(resolve_car(Advice)) for the car problem.
% Top level call.  Initializes working memory; attempts to solve Goal
% with certainty factor; prints results; asks user if they would like a
% trace.

solve(Goal) :- 
    init, print_help,
    solve(Goal,C,[],1),
    nl,write('Solved '),write(Goal),
    write(' With Certainty = '),write(C),nl,nl,
    ask_for_trace(Goal).

% init
% purges all facts from working memory.

init :- retractm(fact(X)), retractm(untrue(X)).

% solve(Goal,CF,Rulestack,Cutoff_context)
% Attempts to solve Goal by backwards chaining on rules;  CF is
% certainty factor of final conclusion; Rulestack is stack of
% rules, used in why queries, Cutoff_context is either 1 or -1
% depending on whether goal is to be proved true or false
% (e.g. not Goal requires Goal be false in oreder to succeed).

solve(true,100,Rules,_).

solve(A,100,Rules,_) :- 
    fact(A).

solve(A,-100,Rules,_) :-
    untrue(A).

solve(not(A),C,Rules,T) :- 
    T2 is -1 * T,
    solve(A,C1,Rules,T2),
    C is -1 * C1.

solve((A,B),C,Rules,T) :- 
    solve(A,C1,Rules,T), 
    above_threshold(C1,T),
    solve(B,C2,Rules,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

solve(A,C,Rules,T) :- 
    rule((A :- B),C1), 
    solve(B,C2,[rule(A,B,C1)|Rules],T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

solve(A,C,Rules,T) :- 
    rule((A), C),
    above_threshold(C,T).

solve(A,C,Rules,T) :- 
    askable(A), 
    not(known(A)), 
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% respond( Answer, Query, CF, Rule_stack).
% respond will process Answer (yes, no, how, why, help).
% asserting to working memory (yes or no)
% displaying current rule from rulestack (why)
% showing proof trace of a goal (how(Goal)
% displaying help (help).
% Invalid responses are detected and the query is repeated.

respond(Bad_answer,A,C,Rules) :- 
    not(member(Bad_answer,[help, yes,no,why,how(_)])),
    write('answer must be either help, (y)es, (n)o, (h)ow(X), (w)hy'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(yes,A,100,_) :- 
    assert(fact(A)).

respond(no,A,-100,_) :- 
    assert(untrue(A)).

respond(why,A,C,[Rule|Rules]) :- 
    display_rule(Rule),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(why,A,C,[]) :-
    write('Back to goal, no more explanation  possible'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,[]).

respond(how(Goal),A,C,Rules) :- 
    respond_how(Goal),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(help,A,C,Rules) :- 
    print_help,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% ask(Query, Answer)
% Writes Query and reads the Answer.  Abbreviations (y, n, h, w) are
% trnslated to appropriate command be filter_abbreviations

ask(Query,Answer) :- 
    display_query(Query),
    read(A),
    filter_abbreviations(A,Answer),!.

% filter_abbreviations( Answer, Command)
% filter_abbreviations will expand Answer into Command.  If
% Answer is not a known abbreviation, then Command = Answer.

filter_abbreviations(y,yes).
filter_abbreviations(n,no).
filter_abbreviations(w,why).
filter_abbreviations(h,help).
filter_abbreviations(h(X),how(X)).
filter_abbreviations(X,X).

% known(Goal)
% Succeeds if Goal is known to be either true or untrue.

known(Goal) :- fact(Goal).
known(Goal) :- untrue(Goal).

% ask_for_trace(Goal).
% Invoked at the end of a consultation, ask_for_trace asks the user if
% they would like a trace of the reasoning to a goal.

ask_for_trace(Goal) :-
    write('Trace of reasoning to goal ? '),
    read(Answer),nl,
    show_trace(Answer,Goal),!.

% show_trace(Answer,Goal)
% If Answer is ``yes'' or ``y,'' show trace will display  a trace
% of Goal, as in a ``how'' query.  Otherwise, it succeeds, doing nothing.

show_trace(yes,Goal) :- respond_how(Goal).

show_trace(y,Goal) :- respond_how(Goal).

show_trace(_,_).

% print_help
% Prints a help screen.

print_help :- 
    write('Exshell allows the following responses to queries:'),nl,nl,
    write('   yes - query is known to be true.'),nl,
    write('   no - query is false.'),nl,
    write('   why - displays rule currently under consideration.'),nl,
    write('   how(X) - if X has been inferred, displays trace of reasoning.'),nl,
    write('   help - prints this message.'),nl,
    write('   Your response may be abbreviated to the first letter and must end with a period (.).'),nl.

% display_query(Goal)
% Shows Goal to user in the form of a query.

display_query(Goal) :-
    write(Goal),
    write('? ').

% display_rule(rule(Head, Premise, CF))
% prints rule in IF...THEN form.

display_rule(rule(Head,Premise,CF)) :-
    write('IF       '),
    write_conjunction(Premise),
    write('THEN     '),
    write(Head),nl,
    write('CF   '),write(CF),
    nl,nl.

% write_conjunction(A)
% write_conjunction will print the components of a rule premise.  If any
% are known to be true, they are so marked.

write_conjunction((A,B)) :-
    write(A), flag_if_known(A),!, nl,
    write('     AND '),
    write_conjunction(B).

write_conjunction(A) :- write(A),flag_if_known(A),!, nl.

% flag_if_known(Goal).
% Called by write_conjunction, if Goal follows from current state
% of working memory, prints an indication, with CF.

flag_if_known(Goal) :- 
    build_proof(Goal,C,_,1), 
    write('     ***Known, Certainty = '),write(C).

flag_if_known(A). 

% Predicates concerned with how queries.

% respond_how(Goal).
% calls build_proof to determine if goal follows from current state of working
% memory.  If it does, prints a trace of reasoning, if not, so indicates.

respond_how(Goal) :- 
    build_proof(Goal,C,Proof,1),
    interpret(Proof),nl,!.

respond_how(Goal) :- 
    build_proof(Goal,C,Proof,-1),
    interpret(Proof),nl,!.

respond_how(Goal) :- 
    write('Goal does not follow at this stage of consultation.'),nl.

% build_proof(Goal, CF, Proof, Cutoff_context).
% Attempts to prove Goal, placing a trace of the proof in Proof.
% Functins the same as solve, except it does not ask for unknown information.
% Thus, it only proves goals that follow from the rule base and the current 
% contents of working memory.

build_proof(true,100,(true,100),_).

build_proof(Goal, 100, (Goal :- given,100),_) :- fact(Goal).

build_proof(Goal, -100, (Goal :- given,-100),_) :- untrue(Goal).

build_proof(not(Goal), C, (not(Proof),C),T) :- 
    T2 is -1 * T,
    build_proof(Goal,C1,Proof,T2),
    C is -1 * C1.

build_proof((A,B),C,(ProofA, ProofB),T) :-
    build_proof(A,C1,ProofA,T),
    above_threshold(C1,T),
    build_proof(B,C2,ProofB,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

build_proof(A, C, (A :- Proof,C),T) :-
    rule((A :- B),C1), 
    build_proof(B, C2, Proof,T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

build_proof(A, C, (A :- true,C),T) :-
    rule((A),C),
    above_threshold(C,T).

% interpret(Proof).
% Interprets a Proof as constructed by build_proof,
% printing a trace for the user.

interpret((Proof1,Proof2)) :-
    interpret(Proof1),interpret(Proof2).

interpret((Goal :- given,C)):-
    write(Goal),
    write(' was given. CF = '), write(C),nl,nl.

interpret((not(Proof), C)) :-
    extract_body(Proof,Goal),
    write('not '),
    write(Goal),
    write(' CF = '), write(C),nl,nl,
    interpret(Proof).

interpret((Goal :- true,C)) :-
    write(Goal),
        write(' is a fact, CF = '),write(C),nl.

interpret(Proof) :-
    is_rule(Proof,Head,Body,Proof1,C),
    nl,write(Head),write(' CF = '),
    write(C), nl,write('was proved using the rule'),nl,nl,
    rule((Head :- Body),CF),
    display_rule(rule(Head, Body,CF)), nl,
    interpret(Proof1).

% isrule(Proof,Goal,Body,Proof,CF)
% If Proof is of the form Goal :- Proof, extracts
% rule Body from Proof.

is_rule((Goal :- Proof,C),Goal, Body, Proof,C) :-
    not(member(Proof, [true,given])),
    extract_body(Proof,Body).

% extract_body(Proof).
% extracts the body of the top level rule from Proof.

extract_body((not(Proof), C), (not(Body))) :-
    extract_body(Proof,Body).

extract_body((Proof1,Proof2),(Body1,Body2)) :-
    !,extract_body(Proof1,Body1),
    extract_body(Proof2,Body2).

extract_body((Goal :- Proof,C),Goal).
    
% Utility Predicates.

retractm(X) :- retract(X), fail.
retractm(X) :- retract((X:-Y)), fail.
retractm(X).

member(X,[X|_]).
member(X,[_|T]) :- member(X,T).

minimum(X,Y,X) :- X =< Y.
minimum(X,Y,Y) :- Y < X.

above_threshold(X,1) :- X >= 20.
above_threshold(X,-1) :- X =< -20.


%%%
%%% The following is the knowledge base for nutrition advice:
%%%

% Top level goal, starts search.
rule((dietician(Advice) :-
	problems(Y), resolve(Y,Advice)),100).

% rules to infer final diagnostic:

rule((problems(no_interest) :-
issues(lack_of_interest)),80).
rule((problems(obesity) :- 
	issues(overweight),not(emotional_eating), not(sweets_desserts_more_than_3_per_week)),90).
rule((problems(obesity1) :- 
	issues(overweight1),not(emotional_eating)),85).
rule((problems(obesity2) :- 
	issues(overweight),not(emotional_eating), sweets_desserts_more_than_3_per_week),90).
rule((problems(emotional_obesity) :- 
	issues(overweight),(emotional_eating)),70).
rule((problems(triglycerides) :-
	issues(cholesterol_problem),cholesterol_problem_Triglycerides),90).
rule((problems(ldl) :- 
	issues(cholesterol_problem), cholesterol_problem_LDL),80).
rule((problems(bp) :- 
	issues(high_blood_pressure)),90).
rule((problems(bp1) :- 
	high_blood_pressure, not(add_salt_to_meals_at_table), not(alcohol_more_than_1_per_day)),90).
rule((problems(bp2) :- 
	high_blood_pressure, not(add_salt_to_meals_at_table), alcohol_more_than_1_per_day),90).
rule((problems(diabetic1) :-
	issues(diabetes), male),80).
rule((problems(diabetic2) :-
	issues(diabetes1)), 90).
rule((problems(diabetic3) :-
	diabetic, not(blood_sugar_above_130mg/dL)),80).
rule((problems(bh1) :-
	issues(osteoprosis1), less_than_2_servings_dairy_products_daily, lessThan_600_IU_vitamin_D_daily, resistance_training_twice_weekly, above_50_yearsOld),80).
rule((problems(bh2) :-
	issues(osteoprosis1), not(less_than_2_servings_dairy_products_daily), lessThan_600_IU_vitamin_D_daily, resistance_training_twice_weekly, above_50_yearsOld),95).
rule((problems(bh3) :-
	issues(osteoprosis1), less_than_2_servings_dairy_products_daily, not(lessThan_600_IU_vitamin_D_daily), resistance_training_twice_weekly, above_50_yearsOld),90).
rule((problems(bh4) :-
	issues(osteoprosis1), less_than_2_servings_dairy_products_daily, lessThan_600_IU_vitamin_D_daily, not(resistance_training_twice_weekly), above_50_yearsOld),80).
rule((problems(bh5) :-
	issues(osteoprosis1), not(less_than_2_servings_dairy_products_daily), not(lessThan_600_IU_vitamin_D_daily), resistance_training_twice_weekly, above_50_yearsOld),80).
rule((problems(bh6) :-
	issues(osteoprosis1), not(less_than_2_servings_dairy_products_daily), lessThan_600_IU_vitamin_D_daily, not(resistance_training_twice_weekly), above_50_yearsOld),90).
rule((problems(bh7) :-
	issues(osteoprosis1), less_than_2_servings_dairy_products_daily, not(lessThan_600_IU_vitamin_D_daily), not(resistance_training_twice_weekly), above_50_yearsOld),95).
rule((problems(bh8) :-
	issues(osteoprosis1), not(less_than_2_servings_dairy_products_daily), not(lessThan_600_IU_vitamin_D_daily), not(resistance_training_twice_weekly), above_50_yearsOld),90).
rule((problems(bh9) :-
	issues(osteoprosis2), less_than_2_servings_dairy_products_daily, lessThan_600_IU_vitamin_D_daily, resistance_training_twice_weekly, above_50_yearsOld),80).
rule((problems(bh10) :-
	issues(osteoprosis2), not(less_than_2_servings_dairy_products_daily), lessThan_600_IU_vitamin_D_daily, resistance_training_twice_weekly, above_50_yearsOld),95).
rule((problems(bh11) :-
	issues(osteoprosis2), less_than_2_servings_dairy_products_daily, not(lessThan_600_IU_vitamin_D_daily), resistance_training_twice_weekly, above_50_yearsOld),95).
rule((problems(bh12) :-
	issues(osteoprosis2), less_than_2_servings_dairy_products_daily, lessThan_600_IU_vitamin_D_daily, not(resistance_training_twice_weekly), above_50_yearsOld),80).
rule((problems(bh13) :-
	issues(osteoprosis2), not(less_than_2_servings_dairy_products_daily), not(lessThan_600_IU_vitamin_D_daily), resistance_training_twice_weekly, above_50_yearsOld),85).
rule((problems(bh14) :-
	issues(osteoprosis2), not(less_than_2_servings_dairy_products_daily), lessThan_600_IU_vitamin_D_daily, not(resistance_training_twice_weekly), above_50_yearsOld),80).
rule((problems(bh15) :-
	issues(osteoprosis2), less_than_2_servings_dairy_products_daily, not(lessThan_600_IU_vitamin_D_daily), not(resistance_training_twice_weekly), above_50_yearsOld),90).
rule((problems(bh16) :-
	issues(osteoprosis2), not(less_than_2_servings_dairy_products_daily), not(lessThan_600_IU_vitamin_D_daily), not(resistance_training_twice_weekly), above_50_yearsOld),95).
rule((problems(bh17) :-
	issues(osteoprosis3), less_than_2_servings_dairy_products_daily, lessThan_600_IU_vitamin_D_daily, resistance_training_twice_weekly, not(above_50_yearsOld)),80).
rule((problems(bh18) :-
	issues(osteoprosis3), not(less_than_2_servings_dairy_products_daily), lessThan_600_IU_vitamin_D_daily, resistance_training_twice_weekly, not(above_50_yearsOld)),80).
rule((problems(bh19) :-
	issues(osteoprosis3), less_than_2_servings_dairy_products_daily, not(lessThan_600_IU_vitamin_D_daily), resistance_training_twice_weekly, not(above_50_yearsOld)),95).
rule((problems(bh20) :-
	issues(osteoprosis3), less_than_2_servings_dairy_products_daily, lessThan_600_IU_vitamin_D_daily, not(resistance_training_twice_weekly), not(above_50_yearsOld)),95).
rule((problems(bh21) :-
	issues(osteoprosis3), not(less_than_2_servings_dairy_products_daily), not(lessThan_600_IU_vitamin_D_daily), resistance_training_twice_weekly, not(above_50_yearsOld)),90).
rule((problems(bh22) :-
	issues(osteoprosis3), not(less_than_2_servings_dairy_products_daily), lessThan_600_IU_vitamin_D_daily, not(resistance_training_twice_weekly), not(above_50_yearsOld)),80).
rule((problems(bh23) :-
	issues(osteoprosis3), less_than_2_servings_dairy_products_daily, not(lessThan_600_IU_vitamin_D_daily), not(resistance_training_twice_weekly), not(above_50_yearsOld)),80).
rule((problems(bh24) :-
	issues(osteoprosis3), not(less_than_2_servings_dairy_products_daily), not(lessThan_600_IU_vitamin_D_daily), not(resistance_training_twice_weekly), not(above_50_yearsOld)),85).
rule((problems(bh25) :-
	issues(osteoprosis4), less_than_2_servings_dairy_products_daily, lessThan_600_IU_vitamin_D_daily, resistance_training_twice_weekly, not(above_50_yearsOld)),90).
rule((problems(bh26) :-
	issues(osteoprosis4), not(less_than_2_servings_dairy_products_daily), lessThan_600_IU_vitamin_D_daily, resistance_training_twice_weekly, not(above_50_yearsOld)),80).
rule((problems(bh27) :-
	issues(osteoprosis4), less_than_2_servings_dairy_products_daily, not(lessThan_600_IU_vitamin_D_daily), resistance_training_twice_weekly, not(above_50_yearsOld)),80).
rule((problems(bh28) :-
	issues(osteoprosis4), less_than_2_servings_dairy_products_daily, lessThan_600_IU_vitamin_D_daily, not(resistance_training_twice_weekly), not(above_50_yearsOld)),90).
rule((problems(bh29) :-
	issues(osteoprosis4), not(less_than_2_servings_dairy_products_daily), not(lessThan_600_IU_vitamin_D_daily), resistance_training_twice_weekly, not(above_50_yearsOld)),80).
rule((problems(bh30) :-
	issues(osteoprosis4), not(less_than_2_servings_dairy_products_daily), lessThan_600_IU_vitamin_D_daily, not(resistance_training_twice_weekly), not(above_50_yearsOld)),85).
rule((problems(bh31) :-
	issues(osteoprosis4), less_than_2_servings_dairy_products_daily, not(lessThan_600_IU_vitamin_D_daily), not(resistance_training_twice_weekly), not(above_50_yearsOld)),85).
rule((problems(bh32) :-
	issues(osteoprosis4), not(less_than_2_servings_dairy_products_daily), not(lessThan_600_IU_vitamin_D_daily), not(resistance_training_twice_weekly), not(above_50_yearsOld)),80).
rule((problems(none) :-
    not(weight_loss), not(diabetic), not(high_blood_pressure), not(cholesterol_problem), not(bone_problem_osteoporosis)),80).


% Rules to infer basic diagnostic.

rule((issues(lack_of_interest) :-
    not(willing_to_change_your_diet)),90).
rule((issues(overweight) :- 
	weight_loss, (bmi(greater_than_25)), not(exercise_more_than_2Hours_30Minutes_aWeek)),70).
rule((issues(overweight1) :- 
	weight_loss, (bmi(greater_than_25)), (exercise_more_than_2Hours_30Minutes_aWeek)),90).
rule((issues(cholesterol_problem) :- 
	cholesterol_problem),80).
rule((issues(high_blood_pressure) :- 
	high_blood_pressure, (add_salt_to_meals_at_table) ),80).
rule((issues(diabetes) :- 
	diabetic, blood_sugar_above_130mg/dL),90).
rule((issues(diabetes1) :- 
	diabetic, not(male)),90).
rule((issues(osteoprosis1) :- 
	bone_problem_osteoporosis, male),85).
rule((issues(osteoprosis2) :- 
	bone_problem_osteoporosis, not(male)),90).
rule((issues(osteoprosis3) :- 
	bone_problem_osteoporosis, male),85).
rule((issues(osteoprosis4) :- 
	bone_problem_osteoporosis, not(male)),90).

% Rules to make reccommendation for patients.

rule(resolve(obesity,'Try to reduce your calorie intake everyday by around 500 kcals. Work towards the Healthy Plate Model at all meals. This means filling half your plate with vegetables (or fruit at breakfast time), filling quarter of your plate with whole grains (e.g. brown rice, quinoa, whole wheat pasta, or bulgar) and the remaining quarter of your plate with lean protein (e.g. grilled fish, chicken breast, lean meat, and beans). Be sure to weigh yourself once a week. Most health benefits occur with at least 150 minutes (2 hours and 30 minutes) a week of moderate intensity physical activity, such as brisk walking. Additional benefits occur with more physical activity. Adults should also do muscle-strengthening activities that are moderate or high intensity and involve all major muscle groups on 2 or more days a week, as these activities provide additional health benefits. Check with your physician before starting an exercise program. A healthy weight loss rate is about 1-2 lbs per week.'),100).
rule(resolve(obesity1,'Try to reduce your calorie intake everyday by around 500 kcals. Work towards the Healthy Plate Model at all meals. This means filling half your plate with vegetables (or fruit at breakfast time), filling quarter of your plate with whole grains (e.g. brown rice, quinoa, whole wheat pasta, or bulgar) and the remaining quarter of your plate with lean protein (e.g. grilled fish, chicken breast, lean meat, and beans). Be sure to weigh yourself once a week. A healthy weight loss rate is about 1-2 lbs per week.'),100).
rule(resolve(obesity2,'Try to reduce your calorie intake everyday by around 500 kcals. Work towards the Healthy Plate Model at all meals. This means filling half your plate with vegetables (or fruit at breakfast time), filling quarter of your plate with whole grains (e.g. brown rice, quinoa, whole wheat pasta, or bulgar) and the remaining quarter of your plate with lean protein (e.g. grilled fish, chicken breast, lean meat, and beans). Be sure to weigh yourself once a week. Most health benefits occur with at least 150 minutes (2 hours and 30 minutes) a week of moderate intensity physical activity, such as brisk walking. Additional benefits occur with more physical activity. Adults should also do muscle-strengthening activities that are moderate or high intensity and involve all major muscle groups on 2 or more days a week, as these activities provide additional health benefits. Check with your physician before starting an exercise program. A healthy weight loss rate is about 1-2 lbs per week. Having sweet and dessert more than 3 times per week increases intake of empty calories and saturated fat – both of which can increase weight and heart disease risk. If you would like to monitor your sugar intake for added health benefits, the American Heart Association recommends women limit sugar consumption to 6 teaspoons (25 grams) per day and men limit to 9 teaspoons (36 grams) per day. '), 100).
rule(resolve(emotional_obesity,'It would be recommended that you see a psychologist to address how your emotions are affecting your eating habits.'),100).
rule(resolve(triglycerides,' Studies show that triglycerides can be lowered by reducing sugar and simple carbohydrates (e.g. white bread, white pasta, etc) and alcohol intake. You may also wish to consider taking a fish oil supplement that provides 1000mg of combined EPA/DHA fatty acids. Speak to your physician about introducing a supplement to your routine'),100).
rule(resolve(ldl, ' One of the most effective dietary strategies to reduce LDL cholesterol is to reduce saturated fat intake. Foods high in saturated fat include: butter, lard, fatty cuts of red meat, coconut/coconut oil, chocolate, and high fat dairy products (e.g. cheese, ice-cream, and high fat yogurt). '),100).
rule(resolve(bp, 'Try to reduce intake of high sodium foods such as canned soups, condiments, cured meats, and salted nuts. Eating out can be a huge source of sodium in one’s diet. Reduce the number of times you eat out to lower your overall sodium intake. Avoid adding salt to your meals. Instead, opt for salt-free seasonings such as Mrs. Dash or similar varieties and cook more with herbs and spices for flavor.'),100).
rule(resolve(bp1, 'Try to reduce intake of high sodium foods such as canned soups, condiments, cured meats, and salted nuts. Eating out can be a huge source of sodium in one’s diet. Reduce the number of times you eat out to lower your overall sodium intake '),100).
rule(resolve(bp2, 'Try to reduce intake of high sodium foods such as canned soups, condiments, cured meats, and salted nuts. Eating out can be a huge source of sodium in one’s diet. Reduce the number of times you eat out to lower your overall sodium intake. Less is best when it comes to alcohol consumption. Although past studies have indicated that moderate alcohol consumption has protective health benefits (e.g., reducing risk of heart disease), recent studies show this may not be true. In fact, alcohol consumption can increase blood pressure and risk for certain types of cancer. According to the US Dietary Guidelines for Americans, to reduce the risk of alcohol-related harm, aim for no more than one drink per day for women and two drinks per day for men (no saving up!)  '),100).
rule(resolve(diabetic1, 'Try to eat three balanced meals per day at regular times and space meals no more than six hours apart. You can have a healthy snack in between if you need to. Limit sugars and sweets such as regular pop, desserts, candies, jam and honey. Always choose higher fiber grains when possible (e.g. brown rice over white rice). Try to manage your blood sugar levels by having 3-4 servings of carbohydrates per meal (serving= half a cup of rice/potatoes)'),100).
rule(resolve(diabetic2, 'Try to eat three balanced meals per day at regular times and space meals no more than six hours apart. You can have a healthy snack in between if you need to. Limit sugars and sweets such as regular pop, desserts, candies, jam and honey. Always choose higher fiber grains when possible (e.g. brown rice over white rice). Try to manage your blood sugar levels by having 2-3 servings of carbohydrates per meal (serving= half a cup of rice/potatoes)'),100).
rule(resolve(diabetic3, 'Try to eat three balanced meals per day at regular times and space meals no more than six hours apart. You can have a healthy snack in between if you need to. Limit sugars and sweets such as regular pop, desserts, candies, jam and honey. Always choose higher fiber grains when possible (e.g. brown rice over white rice).'),100).
rule(resolve(bh1, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) It is recommended to get 600 IU/day vitamin D (check Multivitamin!) '),100).
rule(resolve(bh2, ' recommended calcium is 1000 mg/day. It is recommended to get 600 IU/day vitamin D (check Multivitamin!) '),100).
rule(resolve(bh3, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) '),100).
rule(resolve(bh4, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) It is recommended to get 600 IU/day vitamin D (check Multivitamin!). Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations.  '),100).
rule(resolve(bh5, ' recommended calcium is 1000 mg/day'),100).
rule(resolve(bh6, ' recommended calcium is 1000 mg/day. It is recommended to get 600 IU/day vitamin D (check Multivitamin!). Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations.'),100).
rule(resolve(bh7, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations.  '),100).
rule(resolve(bh8, ' recommended calcium is 1000 mg/day. Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations. '),100).
rule(resolve(bh9, ' recommended calcium is 1200 mg/day. you should aim for 3 dairy servings/day (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt). It is recommended to get 600 IU/day vitamin D (check Multivitamin!)   '),100).
rule(resolve(bh10, 'recommended calcium is 1200 mg/day. It is recommended to get 600 IU/day vitamin D (check Multivitamin!) '),100).
rule(resolve(bh11, 'recommended calcium is 1200 mg/day. you should aim for 3 dairy servings/day (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt)   '),100).
rule(resolve(bh12, 'recommended calcium is 1200 mg/day. you should aim for 3 dairy servings/day (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt). It is recommended to get 600 IU/day vitamin D (check Multivitamin!). Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations.   '),100).
rule(resolve(bh13, 'recommended calcium is 1200 mg/day. '),100).
rule(resolve(bh14, 'recommended calcium is 1200 mg/day. It is recommended to get 600 IU/day vitamin D (check Multivitamin!). Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations. '),100).
rule(resolve(bh15, 'recommended calcium is 1200 mg/day. you should aim for 3 dairy servings/day (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt). Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations.    '),100).
rule(resolve(bh16, 'recommended calcium is 1200 mg/day. Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations.  '),100).
rule(resolve(bh17, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) It is recommended to get 600 IU/day vitamin D (check Multivitamin!)  '),100).
rule(resolve(bh18, ' recommended calcium is 1000 mg/day. It is recommended to get 600 IU/day vitamin D (check Multivitamin!) '),100).
rule(resolve(bh19, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) '),100).
rule(resolve(bh20, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) It is recommended to get 600 IU/day vitamin D (check Multivitamin!). Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations. '),100).
rule(resolve(bh21, ' recommended calcium is 1000 mg/day'),100).
rule(resolve(bh22, ' recommended calcium is 1000 mg/day. It is recommended to get 600 IU/day vitamin D (check Multivitamin!). Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations.'),100).
rule(resolve(bh23, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations.  '),100).
rule(resolve(bh24, ' recommended calcium is 1000 mg/day. Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations. '),100).
rule(resolve(bh25, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) It is recommended to get 600 IU/day vitamin D (check Multivitamin!)  '),100).
rule(resolve(bh26, ' recommended calcium is 1000 mg/day. It is recommended to get 600 IU/day vitamin D (check Multivitamin!) '),100).
rule(resolve(bh27, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) '),100).
rule(resolve(bh28, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) It is recommended to get 600 IU/day vitamin D (check Multivitamin!). Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations. '),100).
rule(resolve(bh29, ' recommended calcium is 1000 mg/day'),100).
rule(resolve(bh30, ' recommended calcium is 1000 mg/day. It is recommended to get 600 IU/day vitamin D (check Multivitamin!). Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations.'),100).
rule(resolve(bh31, ' recommended calcium is 1000 mg/day. Typically, one can reach their calcium needs by having 2 servings of high calcium foods/beverages per day. (serving= 1 cup of milk, 1.5oz of cheese, 3/4 cup of yogurt) Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations. '),100).
rule(resolve(bh32, ' recommended calcium is 1000 mg/day. Weight-bearing exercise and resistance exercise are particularly important for improving bone density and helping to prevent osteoporosis. Speak to your physician or physical therapist for personalized recommendations. '),100).
rule(resolve(none, 'It appears you are on the right track. If you have any specific dietary questions or health concerns, visit your local dietician! '),100).
rule(resolve(no_interest, 'It seems that you are not ready to make changes to your diet just yet. Know that we are always here to help you achieve your goals when you feel that you are ready. Here are some nutrition tips should you be interested: Aim for 4-8 servings of fruits per day (serving = half a cup). Always pick real fruit over fruit juice.  Also, aim for 4-8 servings (serving = half a cup) of vegetables per day (raw, cooked, steamed, boiled) '),100).

% askable descriptions
askable(diabetic). 
askable(weight_loss).
askable(above_50_yearsOld).
askable(male).
askable(bmi(greater_than_25)).
askable(high_blood_pressure).
askable(willing_to_change_your_diet).
askable(exercise_more_than_2Hours_30Minutes_aWeek).
askable(alcohol_more_than_1_per_day).
askable(sweets_desserts_more_than_3_per_week).
askable(emotional_eating).
askable(cholesterol_problem).
askable(cholesterol_problem_Triglycerides).
askable(cholesterol_problem_LDL).
askable(add_salt_to_meals_at_table).
askable(blood_sugar_above_130mg/dL).
askable(bone_problem_osteoporosis).
askable(less_than_2_servings_dairy_products_daily).
askable(lessThan_600_IU_vitamin_D_daily).
askable(resistance_training_twice_weekly).
