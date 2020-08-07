globals
[
  num-infected              ; total number of people infected at any one time
  total-num-infected        ; total number of people infected
  total-num                 ; total number of people
  retail-stores             ; a set of patches that are retail stores
  resturants                ; a set of patches that are resturants
  grocery-stores             ; a set of patches that are grpcery stores
  schools                   ; a set of patches that are schools
  transmission-liklihood    ; probability of transmission in the same patch
  infections-today          ; new infections on a given day

  ; global variables to determine the restrictions on the people
  social-distancing         ; boolean whether social distancing in mandatory
  stay-at-home              ; boolean whether stay-at-home is required
  masks                     ; boolean whether masks are mandatory
  resturant-mode            ; string: could be takeout, outdoor, indoor (half capacity), or full capacity
  retail-mode               ; string: could be closed, curbside, open (half capacity), or full capacity
  grocery-distanced         ; boolean, if grocery stores are socially distanced or not
  schools-open              ; boolean, if schools are open
  current-phase             ; current phase of reopening the simulation is in

  ; variables to play with to refine algorithm
  percent-people-interacted ; % of people in a patch that the infected interacted with
  percent-moving            ; % of people who move against stay-at-home
  initial-prob-trans        ; original probablity of transmission
  grocery-trans-factor      ; How much safer is grocery store than normal interactions
  store-frequency           ; How often people go to a store
]

; Variables that identify patch types
patches-own
[
  store-type                ; effects how restrictions treat the store, could be retail, resturant, grocery, or N/A
  is-school                 ; boolean whether the patch is a school
  max-capacity              ; the maximum number of people allowed in the store
]

; Allows for the referral of a group of turtles as people, and an individual agent as a person
breed [people person]

; Variables used to identify people and run simulation
people-own
[
  epi-status                ; current epidemic state
  when-exposed              ; the tick when the person is exposed
  age                       ; age of person, affects the death-rate
  death-rate                ; the death rate for the persons age group
  previous-patch            ; used to keep track of the patch a person was at before a store or school
  in-store                  ; a boolean to determine if the person is in a store
  in-school                 ; a boolean to determine if the person is in a school
  my-school                 ; if a child, the patch the person goes to school
  at-home                   ; if the person is at home (won't get the virus)
]

to setup
  clear-all
  setup-globals
  setup-patches
  setup-stores
  setup-people
  setup-schools
  reset-ticks
  ; Start the epidemic with x amount of initial infections
  start-epidemic (1 + total-num / 4000)
end

to go
  ; Check if still any infectious
  ; if all? people [epi-status = "susceptible" or epi-status = "immune" or epi-status = "dead"] [stop]
  set infections-today 0

  ; Determine which restrictions to use
  (ifelse (restriction-type = "Virginia") [
    virginia-restrictions
  ] (restriction-type = "California") [
    california-restrictions
  ] (restriction-type = "New York") [
    new-york-restrictions
  ] (restriction-type = "Florida") [
    florida-restrictions
  ] ; else
  [
    custom-restrictions
  ])
  move
  update-status
  transmit-infection
  tick
end


; Start the epidemic with the number of exposed people
to start-epidemic [#exposed]
  ask n-of #exposed people with [epi-status = "susceptible"]
  [
    set-status-exposed
  ]
end


; ===============================================================================================================
;
; MOVE FUNCTIONS
;
; ===============================================================================================================


; Moves specified proportion of people in a random direction
; If they hit a boundry turn the away so they do not gather at boudries
; If they hit a boundry, there is an increased chance of contraction of virus
; Allows for people to go to the store as well (average of once per week)
to move
  ; If dead, do not move, immune does not matter so don't move for speed
  let movers people with [ epi-status = "susceptible" or epi-status = "exposed"
    or epi-status = "infectious"]
  ask movers
  [
    ; Change the heading of the person, return true if they left the boundry
    let left-boundry (set-heading self)

    ; Let some people go out to stores or school, return if they went out
    let went-out (go-out self)

    ; If they didn't go out move forward or not at all
    (ifelse (not went-out) [
      (ifelse (stay-at-home and (random-float 1 < percent-moving )) [
        set at-home true
      ] ; else move randomly
      [
        set at-home false
        forward random-float 2 + 1
      ])
    ] ; else set at-home false
    [
      set at-home false
    ])

    ; If the person left the boundry, they could have gotten infected
    if (left-boundry and (not at-home)) [
      let prob-infected-outside transmission-liklihood * (num-infected / total-num)
      if (random-float 1 < prob-infected-outside) [
        set-status-exposed
      ]
    ]
  ]
end

; Set the heading of a person passed as a parameter, return whether they left the boundry
to-report set-heading [heading-to-be-set]
  ; Boolean to see if the person could have gotten infected leaving
  let left-boundry false
  ; If on a boundry, face away from the boundry, also need to check for corners
  (ifelse (pxcor = min-pxcor) and (pycor = min-pycor) [ ; bottom left
    set heading random 90
    set left-boundry true
  ] (pxcor = min-pxcor) and (pycor = max-pycor) [ ; top left
    set heading random 90 + 90
    set left-boundry true
  ] (pxcor = max-pxcor) and (pycor = max-pycor) [ ; top right
    set heading random 90 + 180
    set left-boundry true
  ] (pxcor = max-pxcor) and (pycor = min-pycor) [ ; bottom right
    set heading random 90 + 270
    set left-boundry true
  ] (abs pxcor = max-pxcor) [
    set heading (- heading)
    set left-boundry true
  ] (abs pycor = max-pycor) [
    set heading (180 - heading)
    set left-boundry true
  ] ; else
  [
    ; Set a random heading
    set heading random 360
    set left-boundry false
  ])

  ; Return whether the person left the boundry or not
  report left-boundry
end

; Lets a person go out (to school, grocery store, retail, or resturant) if they meet
; certain criteria, returns a boolean of if they went out
to-report go-out [to-go-out]
  ; to return: whether the turtle went out or not
  let to-return false

  ; If the person is a child, it is not a weekend and schools are open go to school
  (ifelse (((age <= 18) and (age > 2)) ; if they are children
    and ((ticks mod 7 != 0) and (ticks mod 7 != 6)) ; if its not a weekend
    and (schools-open) and ((ticks < 93) or (ticks > 170))) [ ; if its not the summer
    ; If not in school go to school
    if (not in-school) [
      ; If the child is not at school and not in the same patch as its previous set its
      ; previous patch to its current patch
      if ((patch-here != previous-patch) and (patch-here != my-school)) [
        set previous-patch patch-here
      ]
      set in-school true
      move-to my-school
    ]
    set to-return true
  ] ((in-store) or (in-school)) [ ; If in a store or school go home
    set in-store false
    set in-school false
    move-to previous-patch
    set at-home true
  ] (random-float 1 < store-frequency) [ ; go out on average twice a week per person
    ; If the person went out set the value to true
    set to-return (go-to-a-store self)
  ])
  ; Report if the person went out
  report to-return
end

;
to-report go-to-a-store [goer-to-store]
  ; to-return: whether the person was able to go to a store (full capacity or not)
  let to-return false

  ; determine what kind of store the person will go to
  let which-store-type random-float 1

  ; the actual patch / store that the person will go to, preliminarily set to current patch
  let the-store patch-here

  ; set the type of store to go to if they are not closed
  (ifelse ((which-store-type <= .33) and ((retail-mode != "closed") and (retail-mode != "curbside")) and (total-num > 400)) [
    set the-store one-of retail-stores
  ] ((which-store-type <= .66) and (which-store-type > .33) and (resturant-mode != "takeout")) [
    set the-store one-of resturants
  ] (which-store-type > .66) [
    set the-store one-of grocery-stores
  ] ; else exit
  [
    report false
  ])

  ; See how many people are already in the store
  let current-capacity (count people-on the-store)

  ; If the store is under capacity the person can go to it, otherwise it does nothing
  if (current-capacity <= ([max-capacity] of the-store)) [
    if ((patch-here != previous-patch) and (patch-here != my-school)) [
      set previous-patch patch-here
    ]
    set in-store true
    move-to the-store
    set to-return true
  ]
  ; Report whether the person went out
  report to-return
end

; If infected there is a probability of exposing other people
; in the same patch (about 100 yds)
to transmit-infection
  ; Make a agentset of infectious people
  let transmitters people with [epi-status = "infectious"]

  ask transmitters
  [
    ; All people that are susceptible in transmitters' patches
    let people-in-patch (people-here with [epi-status = "susceptible" and (not at-home)])
    ask n-of ((count people-in-patch) * percent-people-interacted) people-in-patch ; Only 1/2 of people in the patch can get infected
    [
      ; Set the probablity of infection to some number
      let prob-infect transmission-liklihood

      ; If the person is in a grocery store and it is distanced, transmission is low
      if (([store-type] of patch-here = "grocery") and grocery-distanced) [
        set prob-infect (prob-infect - (initial-prob-trans * grocery-trans-factor))
      ]

      ; If the person is infected change their epi-status
      if random-float 1 < prob-infect
      [
        set-status-infected
      ]
    ]
  ]
end

to adjust-transmission-prob
  ; reset the probablity back to .06 and adjust from there
  let new-prob initial-prob-trans

  if (masks) [
    set new-prob (new-prob - (initial-prob-trans / 3))
  ]

  if (social-distancing) [
    set new-prob (new-prob - (initial-prob-trans / 3))
  ]

  set transmission-liklihood new-prob
end

; ===============================================================================================================
;
; CHANGE EPI STATUS FUNCTIONS
;
; ===============================================================================================================


; If it has been 7-21 days since infection set the status to immune
; If it has been 2-14 days after exposure set the status to infectious
to update-status
  ; Get all people with an infectious status
  let infectious people with [epi-status = "infectious"]
  ask infectious
  [
    ; If it has been 7-21 days (random) since the infection set to immune
    if (when-exposed + random 14 + 7 < ticks)
    [
      set-status-dead-or-immune
    ]
  ]

  ; Get all people with an exposed status
  let exposed people with [epi-status = "exposed"]
  ask exposed
  [
    ; If it has been 2-14 days (random) since the exposure set to exposed
    if (when-exposed + random 12 + 2 < ticks)
    [
      set-status-infected
    ]
  ]
end

; Set the status of a person to exposed
to set-status-exposed
  ; Change the status
  set epi-status "exposed"
  ; Change the appearance to exposed
  set color orange
  set size 0.7
  set shape "dot"
  set when-exposed ticks
end

; Set the status of a person to infected
to set-status-infected
  ; Actually change the status
  set epi-status "infectious"
  ; Change the look of the peson to make it obvious they are infected
  set color red
  set size 1
  set shape "dot"
  set when-exposed ticks
  ; Change the total number of infected to plus one
  set num-infected num-infected + 1
  ; Increase the new infection counter
  set infections-today (infections-today + 1)
  ; Increse the total infections counter over all time
  set total-num-infected (total-num-infected + 1)
end

to set-status-dead-or-immune
  (ifelse (death-rate > random-float 1) [
    ; Change the epi-status
    set epi-status "dead"
    ; Change the look of the person to make it obvious dead
    set color grey
    set size 0.5
    set shape "dot"
  ] ; else
  [
    ; Change the epi-status
    set epi-status "immune"
    ; Change the look of the person to make it obvious immune
    set color green
    set size 0.5
    set shape "square"
  ])
  ; Change the total infected to infected minus 1
  set num-infected num-infected - 1
end


; ===============================================================================================================
;
; STATE RESTRICTION FUNCTIONS
;
; ===============================================================================================================

to new-york-restrictions
  ; start of lockdown state-wide (March 22nd)
  (ifelse (ticks = 9) [
    set masks true
    set stay-at-home true
    set social-distancing true
    set resturant-mode "takeout"
    set retail-mode "closed"
    set grocery-distanced true
    set schools-open false
    set current-phase "Lockdown"

    ; Ask all people in a school or store to go home
    ask people with [in-school = true or in-store = true]
    [
      set in-store false
      set in-school false
      move-to previous-patch
    ]
    ; Adjust the transmission probablity
    adjust-transmission-prob
  ] (ticks = 65) [ ; Phase 1: May 26th for most counties, only change is curbside retail
    set retail-mode "curbside"
    set current-phase "Phase 1"
  ] (ticks = 79) [ ; Phase 2: June 9th for most counties, resturants are outdoor, retail open
    set resturant-mode "outdoor"
    set retail-mode "open"
    set current-phase "Phase 2"

    ; Change the seating capacities of resturants and retail
    ask patches with [store-type = "resturant" or store-type = "retail"] [
      ; set capacity to 1/4 of normal capactiy
      set max-capacity (max-capacity / 4)
    ]
  ] (ticks = 93) [ ; Phase 3: June 23rd for most counties, resturants are indoor
    set resturant-mode "indoor"
    set current-phase "Phase 3"

    ; Change max capacity of resturants and retail
    ask patches with [store-type = "resturant" or store-type = "retail"] [
      ; set capacity to 1/2 of normal capactiy
      set max-capacity (max-capacity * 2)
    ]
  ] (ticks = 107) [ ; Phase 4: July 7th for most counties, schools open back up
    set schools-open true
    set current-phase "Phase 4"
  ])
end

to virginia-restrictions
  ; start of lockdown state-wide (April 1st)
  (ifelse (ticks = 9) [
    set masks true
    set stay-at-home true
    set social-distancing true
    set resturant-mode "takeout"
    set retail-mode "curbside"
    set grocery-distanced true
    set schools-open false
    set current-phase "Lockdown"

    ; Ask all people in a school or store to go home
    ask people with [in-school = true or in-store = true]
    [
      set in-store false
      set in-school false
      move-to previous-patch
    ]
    ; Adjust the transmission probablity
    adjust-transmission-prob
  ] (ticks = 54) [ ; Phase 1: May 15th for most counties, open retail and resturants
    set retail-mode "open"
    set resturant-mode "outdoor"
    set current-phase "Phase 1"

    ; Change the seating capacities of resturants and retail
    ask patches with [store-type = "resturant" or store-type = "retail"] [
      ; set capacity to 1/4 of normal capactiy
      (ifelse (store-type = "resturant") [
        set max-capacity (max-capacity / 4) ; outdoor seating
      ] ; else
      [
        set max-capacity (max-capacity / 2)
      ])

    ]
  ] (ticks = 82) [ ; Phase 2: June 12th for most counties, resturants are indoor
    set resturant-mode "indoor"
    set current-phase "Phase 2"

    ; Change the seating capacities of resturants
    ask patches with [store-type = "resturant"] [
      ; set capacity to 1/4 of normal capactiy
      set max-capacity (max-capacity * 2)
    ]
  ] (ticks = 93) [ ; Phase 3: July 1st for most counties, increased capacities
    set resturant-mode "indoor"
    set current-phase "Phase 3"

    ; Change max capacity of resturants and retail
    ask patches with [store-type = "resturant" or store-type = "retail"] [
      ; set capacity to 3/4 of normal capactiy
      set max-capacity (max-capacity * 1.5)
    ]
  ])
end

to california-restrictions
  ; start of lockdown state-wide (March 20th)
  (ifelse (ticks = 9) [
    set masks true
    set stay-at-home true
    set social-distancing true
    set resturant-mode "takeout"
    set retail-mode "curbside"
    set grocery-distanced true
    set schools-open false
    set current-phase "Lockdown / Phase 1"

    ; Ask all people in a school or store to go home
    ask people with [in-school = true or in-store = true]
    [
      set in-store false
      set in-school false
      move-to previous-patch
    ]
    ; Adjust the transmission probablity
    adjust-transmission-prob
  ] (ticks = 59) [ ; Phase 2: May 8th for most counties
    set retail-mode "open"
    set resturant-mode "outdoor"
    set current-phase "Phase 2"

    ; Change the seating capacities of resturants and retail
    ask patches with [store-type = "resturant" or store-type = "retail"] [
      ; set capacity to 1/4 of normal capactiy
      set max-capacity (max-capacity / 4)
    ]
  ] (ticks = 94) [ ; Phase 3: June 12th for most counties
    set resturant-mode "indoor"
    set current-phase "Phase 3"

    ; Change the seating capacities of resturants and retail
    ask patches with [store-type = "resturant" or store-type = "retail"] [
      ; set capacity to 1/4 of normal capactiy
      set max-capacity (max-capacity * 2)
    ]
  ] (ticks = 125) [ ; Reclosure: July 13th back to phase 2
    set resturant-mode "outdoor"
    set current-phase "Reclosure / Phase 2"

    ; Change the seating capacities of resturants and retail
    ask patches with [store-type = "resturant" or store-type = "retail"] [
      ; set capacity to 1/4 of normal capactiy
      set max-capacity (max-capacity / 2)
    ]
    ; Don't know what the next phase will be
;  ] (ticks = 107) [ ; Phase 4: July 7th for most counties, schools open back up
;    set schools-open true
  ])
end

to florida-restrictions
  ; start of lockdown state-wide (March 20th), only resturants and bars are closed
  (ifelse (ticks = 10) [
    set masks true
    set social-distancing true
    set resturant-mode "takeout"
    set schools-open false
    set current-phase "Closed Resturants"

    ; Ask all people in a school and resturants to go home
    ask people with [in-school = true or (in-store = true
      and ([store-type] of patch-here = "resturant"))]
    [
      set in-school false
      set in-store false
      move-to previous-patch
    ]

    ; Adjust the transmission probablity
    adjust-transmission-prob
  ] (ticks = 14 and pop-density >= 1500) [ ; Start of stay-at-home orders for large counties
    set stay-at-home true
    set retail-mode "curbside"
    set grocery-distanced true
    set current-phase "Large Lockdown"

    ; Ask all people in a store to go home
    ask people with [in-store = true]
    [
      set in-store false
      move-to previous-patch
    ]
  ] (ticks = 21 and pop-density < 1500) [ ; Lockdown for the rest of the counties
    set stay-at-home true
    set retail-mode "curbside"
    set grocery-distanced true
    set current-phase "All Lockdown"

    ; Ask all people in a store to go home
    ask people with [in-store = true]
    [
      set in-store false
      move-to previous-patch
    ]
  ] (ticks = 69) [ ; Phase 1: May 18th for most counties, half capacity for retail and resturant
    set resturant-mode "outdoor"
    set retail-mode "open"
    set current-phase "Phase 1"

    ; Change the seating capacities of resturants and retail
    ask patches with [store-type = "resturant" or store-type = "retail"] [
      ; set capacity to 1/4 of normal capactiy
      set max-capacity (max-capacity / 4)
    ]
  ] (ticks = 87) [ ; Phase 2: June 5th for most counties, resturants are indoor, retail open
    set resturant-mode "indoor"
    set retail-mode "open"
    set schools-open true
    set current-phase "Phase 2"

    ; Change the seating capacities of resturants and retail
    ask patches with [store-type = "resturant" or store-type = "retail"] [
      ; set capacity to 1/2 of normal capactiy
      set max-capacity (max-capacity * 2)
    ]
;  ] (ticks = 97) [ ; Phase 3: no date given yet
;    set resturant-mode "full capacity"
;    set retail-mode "full capacity"
;    set stay-at-home false
;
;    ; Change max capacity of resturants and retail
;    ask patches with [store-type = "resturant" or store-type = "retail"] [
;      ; set capacity to normal capactiy
;      set max-capacity (max-capacity * 2)
;    ]
  ])
end

to custom-restrictions
  ; start of lockdown
  (ifelse (ticks = lockdown-start-day) [
    set masks masks-lockdown
    set stay-at-home stay-at-home-lockdown
    set social-distancing social-distance-lockdown
    set resturant-mode resturant-mode-lockdown
    set retail-mode retail-mode-lockdown
    set grocery-distanced grocery-distance-lockdown
    set schools-open schools-open-lockdown
    set current-phase "Lockdown"

    ; Move people home from schools and stores
    move-home

    ; Adjust the transmission probablity
    adjust-transmission-prob

  ] (ticks = phase1-start-day) [ ; Phase 1
    set masks masks-phase1
    set stay-at-home stay-at-home-phase1
    set social-distancing social-distance-phase1
    set resturant-mode resturant-mode-phase1
    set retail-mode retail-mode-phase1
    set grocery-distanced grocery-distance-phase1
    set schools-open schools-open-phase1
    set current-phase "Phase 1"

    ; Move people home from schools and stores
    move-home

    ; Adjust the transmission probablity
    adjust-transmission-prob

  ] (ticks = phase2-start-day) [ ; Phase 2
    set masks masks-phase2
    set stay-at-home stay-at-home-phase2
    set social-distancing social-distance-phase2
    set resturant-mode resturant-mode-phase2
    set retail-mode retail-mode-phase2
    set grocery-distanced grocery-distance-phase2
    set schools-open schools-open-phase2
    set current-phase "Phase 2"

    ; Move people home from schools and stores
    move-home

    ; Adjust the transmission probablity
    adjust-transmission-prob

  ] (ticks = phase3-start-day) [ ; Phase 3
    set masks masks-phase3
    set stay-at-home stay-at-home-phase3
    set social-distancing social-distance-phase3
    set resturant-mode resturant-mode-phase3
    set retail-mode retail-mode-phase3
    set grocery-distanced grocery-distance-phase3
    set schools-open schools-open-phase3
    set current-phase "Phase 3"

    ; Move people home from schools and stores
    move-home

    ; Adjust the transmission probablity
    adjust-transmission-prob

  ] (ticks = phase4-start-day) [ ; Phase 4
    set masks masks-phase4
    set stay-at-home stay-at-home-phase4
    set social-distancing social-distance-phase4
    set resturant-mode resturant-mode-phase4
    set retail-mode retail-mode-phase4
    set grocery-distanced grocery-distance-phase4
    set schools-open schools-open-phase4
    set current-phase "Phase 4"

    ; Move people home from schools and stores
    move-home

    ; Adjust the transmission probablity
    adjust-transmission-prob

  ] (ticks = phase5-start-day) [ ; Phase 5
    set masks masks-phase5
    set stay-at-home stay-at-home-phase5
    set social-distancing social-distance-phase5
    set resturant-mode resturant-mode-phase5
    set retail-mode retail-mode-phase5
    set grocery-distanced grocery-distance-phase5
    set schools-open schools-open-phase5
    set current-phase "Phase 5"

    ; Move people home from schools and stores
    move-home

    ; Adjust the transmission probablity
    adjust-transmission-prob

  ])
end

to move-home
  ; If schools are closed ask all people in school home
    if (not schools-open) [
      ask people with [in-school = true]
      [
        set in-school false
        move-to previous-patch
      ]
    ]

    ; If resturants are closed ask all people in resturants home
    if (resturant-mode = "takeout") [
    ask people with [(in-store = true and ([store-type] of patch-here = "resturant"))]
      [
        set in-store false
        move-to previous-patch
      ]
    ]

    ; If retail is closed ask all people in retail stores home
    if (retail-mode = "closed") [
      ask people with [(in-store = true and ([store-type] of patch-here = "retail"))]
      [
        set in-store false
        move-to previous-patch
      ]
    ]
end

; ===============================================================================================================
;
; SETUP FUNCTIONS
;
; ===============================================================================================================


; Essentially just set the patch color to white
to setup-patches
  ask patches
  [
    set pcolor white
    set store-type "N/A"
    set is-school false
  ]
end

; Declare the initial values of global variables
to setup-globals
  ; Varaibles to manipulate and test
  set percent-people-interacted .66
  set percent-moving 0.80
  set initial-prob-trans 0.6
  set grocery-trans-factor 0.15
  set store-frequency 0.25

  set total-num pop-density * 5
  set transmission-liklihood initial-prob-trans
  set social-distancing false
  set stay-at-home false
  set masks false
  set resturant-mode "full capacity"
  set retail-mode "full capacity"
  set grocery-distanced false
  set schools-open true
  set current-phase "Open"
end

; Setup the patches that are stores and schools
to setup-stores
  ; Set up the number of each type of grocery store
  let num-retail (total-num / 400)
  let num-resturant (total-num / 500 + 1)
  let num-grocery (total-num / 5000 + 1)

  ; Set up the retail stores
  ask n-of num-retail patches with [pcolor = white] [
    set store-type "retail"
    set pcolor yellow + 2
    set max-capacity (total-num / num-retail / 7)
  ]

  ; Set up the resturants
  ask n-of num-resturant patches with [pcolor = white] [
    set store-type "resturant"
    set pcolor red + 2
    set max-capacity (total-num / num-resturant / 7)
  ]

  ; Set up the grocery stores
  ask n-of num-grocery patches with [pcolor = white] [
    set store-type "grocery"
    set pcolor green + 2
    set max-capacity (total-num / num-grocery / 10)
  ]

  ; Make a set of all the retail, resturant, and grocery patches
  set retail-stores patches with [pcolor = yellow + 2]
  set resturants patches with [pcolor = red + 2]
  set grocery-stores patches with [pcolor = green + 2]
end

; Assign a random school to each person under 18, must be done after setup-people is complete
to setup-schools
  ; Set up the number of schools (about 1 per 600 kids with at least 1)
  let num-children count people with [age <= 18]
  let num-schools (num-children / 600 + 1)

  ; Set up the schools
  ask n-of num-schools patches with [pcolor = white] [
    set is-school true
    set pcolor violet + 2
  ]

  ; Make a set of all the school patches
  set schools patches with [pcolor = violet + 2]

  ; Assign a school to each child
  ask people with [age <= 18] [
    set my-school one-of schools
  ]
end

to setup-people
  ; Act like the simulation zone is just a five square mile space in the county with uniform
  ; population density
  create-people total-num
  ask people
  [
    ; Setup variables
    set epi-status "susceptible"
    set in-store false
    set in-school false
    set previous-patch patch-here
    set at-home false

    ; Set the color, size, and shape of every person
    set color blue
    set size 0.5
    set shape "default"
    ; Randomly spread out the people around the square
    setxy random-xcor random-ycor
  ]
  ; A variable that allows for percentage overflow, just divide given percents by total
  let total-pct (children-pct + twenties-pct + thirties-pct + fourties-pct + fifties-pct + sixties-pct + seventies-pct + eighty-plus-pct)

  ; Set the ages of people by sliders

  ; Children: people aged 0-19
  ask n-of (total-num * (children-pct / total-pct)) people [
    set age random 19
    set death-rate 0.002
  ]

  ; People aged 20-29
  ask n-of (total-num * (twenties-pct / total-pct)) people [
    set age random 9 + 20
    set death-rate 0.002
  ]

  ; People aged 30-39
  ask n-of (total-num * (thirties-pct / total-pct)) people [
    set age random 9 + 30
    set death-rate 0.002
  ]

  ; People aged 40-49
  ask n-of (total-num * (fourties-pct / total-pct)) people [
    set age random 9 + 40
    set death-rate 0.004
  ]

  ; People aged 50-59
  ask n-of (total-num * (fifties-pct / total-pct)) people [
    set age random 9 + 50
    set death-rate 0.006
  ]

  ; People aged 60-69
  ask n-of (total-num * (sixties-pct / total-pct)) people [
    set age random 9 + 60
    set death-rate 0.025
  ]

  ; People aged 70-79
  ask n-of (total-num * (seventies-pct / total-pct)) people [
    set age random 9 + 70
    set death-rate 0.08
  ]

  ; People aged 80-89 (treat it like everyone above 80)
  ask n-of (total-num * (eighty-plus-pct / total-pct)) people [
    set age random 9 + 80
    set death-rate 0.16
  ]
end
@#$#@#$#@
GRAPHICS-WINDOW
210
10
628
429
-1
-1
10.0
1
10
1
1
1
0
0
0
1
-20
20
-20
20
1
1
1
days
30.0

BUTTON
16
28
79
61
NIL
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
11
75
195
108
pop-density
pop-density
50
5000
2280.0
10
1
people/sq. mile
HORIZONTAL

BUTTON
104
28
167
61
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

PLOT
1102
24
1474
207
Population
Time (days)
Percentage of People
0.0
10.0
0.0
100.0
true
true
"" ""
PENS
"susceptible" 1.0 0 -13345367 true "" "plot (count people with [epi-status =\n \"susceptible\"] / total-num) * 100"
"infected" 1.0 0 -955883 true "" "plot (count people with [epi-status = \n\"infectious\" or epi-status = \"exposed\"]\n/ total-num) * 100"
"recovered" 1.0 0 -10899396 true "" "plot (count people with [epi-status =\n\"immune\"] / total-num) * 100"
"deceased" 1.0 0 -7500403 true "" "plot (count people with [epi-status =\n\"dead\"] / total-num) * 100"

MONITOR
11
129
196
174
Number of people susceptible 
count people with [epi-status = \"susceptible\"]
0
1
11

MONITOR
12
185
194
230
Number of people infected
count people with [epi-status = \"infectious\" or\nepi-status = \"exposed\"]
17
1
11

MONITOR
10
239
196
284
Number of people recovered
count people with [epi-status = \"immune\"]
0
1
11

TEXTBOX
66
459
136
477
AGE DATA
14
0.0
1

SLIDER
11
480
183
513
children-pct
children-pct
0
100
24.8
.1
1
%
HORIZONTAL

SLIDER
10
529
182
562
twenties-pct
twenties-pct
0
100
13.7
.1
1
%
HORIZONTAL

SLIDER
12
578
184
611
thirties-pct
thirties-pct
0
100
13.5
.1
1
%
HORIZONTAL

SLIDER
11
627
183
660
fourties-pct
fourties-pct
0
100
12.3
.1
1
%
HORIZONTAL

SLIDER
8
674
180
707
fifties-pct
fifties-pct
0
100
12.9
.1
1
%
HORIZONTAL

SLIDER
11
722
183
755
sixties-pct
sixties-pct
0
100
11.6
.1
1
%
HORIZONTAL

SLIDER
8
768
180
801
seventies-pct
seventies-pct
0
100
7.2
.1
1
%
HORIZONTAL

SLIDER
10
814
182
847
eighty-plus-pct
eighty-plus-pct
0
100
4.0
.1
1
%
HORIZONTAL

MONITOR
10
292
197
337
Number of people deceased
count people with [epi-status = \"dead\"]
17
1
11

CHOOSER
781
13
919
58
restriction-type
restriction-type
"Virginia" "New York" "California" "Florida" "Custom"
4

PLOT
1101
226
1475
376
New Cases
Time (days)
Number of Cases
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"Infected" 1.0 1 -955883 true "" "plot infections-today"

MONITOR
10
347
197
392
Total number of people infected
total-num-infected
0
1
11

PLOT
1101
401
1479
551
Total Infections
Time (days)
Number of People
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"infected" 1.0 0 -955883 true "" "plot total-num-infected"

SWITCH
649
151
827
184
masks-lockdown
masks-lockdown
0
1
-1000

SWITCH
650
225
828
258
stay-at-home-lockdown
stay-at-home-lockdown
0
1
-1000

SWITCH
650
188
827
221
social-distance-lockdown
social-distance-lockdown
0
1
-1000

SWITCH
651
299
827
332
grocery-distance-lockdown
grocery-distance-lockdown
0
1
-1000

SWITCH
650
262
827
295
schools-open-lockdown
schools-open-lockdown
1
1
-1000

CHOOSER
651
389
829
434
retail-mode-lockdown
retail-mode-lockdown
"Closed" "Curbside" "Open" "Full Capacity"
0

CHOOSER
650
337
828
382
resturant-mode-lockdown
resturant-mode-lockdown
"Takeout" "Outdoor" "Indoor" "Full Capacity"
0

SLIDER
648
114
826
147
lockdown-start-day
lockdown-start-day
1
100
9.0
1
1
NIL
HORIZONTAL

TEXTBOX
707
94
782
112
Lockdown
14
0.0
1

TEXTBOX
779
67
929
91
Custom Restrictions:
16
0.0
1

SLIDER
876
113
1048
146
phase1-start-day
phase1-start-day
1
365
65.0
1
1
NIL
HORIZONTAL

SWITCH
875
150
1049
183
masks-phase1
masks-phase1
0
1
-1000

SWITCH
875
187
1050
220
social-distance-phase1
social-distance-phase1
0
1
-1000

SWITCH
874
224
1049
257
stay-at-home-phase1
stay-at-home-phase1
0
1
-1000

SWITCH
875
262
1051
295
schools-open-phase1
schools-open-phase1
1
1
-1000

SWITCH
874
300
1052
333
grocery-distance-phase1
grocery-distance-phase1
0
1
-1000

CHOOSER
874
339
1052
384
resturant-mode-phase1
resturant-mode-phase1
"Takeout" "Outdoor" "Indoor" "Full Capacity"
1

CHOOSER
874
390
1052
435
retail-mode-phase1
retail-mode-phase1
"Closed" "Curbside" "Open" "Full Capacity"
1

TEXTBOX
936
94
995
112
Phase 1
14
0.0
1

SLIDER
655
494
827
527
phase2-start-day
phase2-start-day
1
365
82.0
1
1
NIL
HORIZONTAL

SWITCH
655
533
828
566
masks-phase2
masks-phase2
0
1
-1000

SWITCH
656
572
829
605
social-distance-phase2
social-distance-phase2
0
1
-1000

SWITCH
655
610
830
643
stay-at-home-phase2
stay-at-home-phase2
0
1
-1000

SWITCH
656
648
829
681
schools-open-phase2
schools-open-phase2
1
1
-1000

SWITCH
655
687
832
720
grocery-distance-phase2
grocery-distance-phase2
0
1
-1000

CHOOSER
655
726
831
771
resturant-mode-phase2
resturant-mode-phase2
"Takeout" "Outdoor" "Indoor" "Full Capacity"
1

CHOOSER
655
777
832
822
retail-mode-phase2
retail-mode-phase2
"Closed" "Curbside" "Open" "Full Capacity"
2

TEXTBOX
716
471
773
489
Phase 2
14
0.0
1

SLIDER
875
494
1055
527
phase3-start-day
phase3-start-day
1
365
100.0
1
1
NIL
HORIZONTAL

SWITCH
877
534
1057
567
masks-phase3
masks-phase3
0
1
-1000

SWITCH
878
572
1057
605
social-distance-phase3
social-distance-phase3
0
1
-1000

SWITCH
878
610
1059
643
stay-at-home-phase3
stay-at-home-phase3
0
1
-1000

SWITCH
878
649
1061
682
schools-open-phase3
schools-open-phase3
1
1
-1000

SWITCH
877
688
1062
721
grocery-distance-phase3
grocery-distance-phase3
0
1
-1000

CHOOSER
877
727
1062
772
resturant-mode-phase3
resturant-mode-phase3
"Takeout" "Outdoor" "Indoor" "Full Capacity"
2

CHOOSER
878
779
1062
824
retail-mode-phase3
retail-mode-phase3
"Closed" "Curbside" "Open" "Full Capacity"
2

TEXTBOX
942
471
994
489
Phase 3
14
0.0
1

SLIDER
655
882
831
915
phase4-start-day
phase4-start-day
1
365
44.0
1
1
NIL
HORIZONTAL

SWITCH
655
920
832
953
masks-phase4
masks-phase4
0
1
-1000

SWITCH
655
960
832
993
social-distance-phase4
social-distance-phase4
0
1
-1000

SWITCH
655
1000
833
1033
stay-at-home-phase4
stay-at-home-phase4
0
1
-1000

SWITCH
656
1039
834
1072
schools-open-phase4
schools-open-phase4
0
1
-1000

SWITCH
653
1078
834
1111
grocery-distance-phase4
grocery-distance-phase4
0
1
-1000

CHOOSER
654
1117
834
1162
resturant-mode-phase4
resturant-mode-phase4
"Takeout" "Outdoor" "Indoor" "Full Capacity"
0

CHOOSER
654
1168
834
1213
retail-mode-phase4
retail-mode-phase4
"Closed" "Curbside" "Open" "Full Capacity"
0

TEXTBOX
715
859
769
877
Phase 4
14
0.0
1

SLIDER
879
880
1064
913
phase5-start-day
phase5-start-day
1
365
365.0
1
1
NIL
HORIZONTAL

SWITCH
879
921
1065
954
masks-phase5
masks-phase5
1
1
-1000

SWITCH
879
961
1066
994
social-distance-phase5
social-distance-phase5
1
1
-1000

SWITCH
881
1000
1067
1033
stay-at-home-phase5
stay-at-home-phase5
1
1
-1000

SWITCH
881
1039
1068
1072
schools-open-phase5
schools-open-phase5
0
1
-1000

SWITCH
881
1077
1068
1110
grocery-distance-phase5
grocery-distance-phase5
1
1
-1000

CHOOSER
882
1117
1066
1162
resturant-mode-phase5
resturant-mode-phase5
"Takeout" "Outdoor" "Indoor" "Full Capacity"
3

CHOOSER
883
1169
1067
1214
retail-mode-phase5
retail-mode-phase5
"Closed" "Curbside" "Open" "Full Capacity"
3

MONITOR
209
454
311
499
Resturant Mode
resturant-mode
17
1
11

MONITOR
318
454
422
499
Retail Mode
retail-mode
17
1
11

MONITOR
428
454
528
499
Masks Required
masks
17
1
11

MONITOR
533
454
630
499
Social Distancing?
social-distancing
17
1
11

MONITOR
209
509
311
554
Stay at Home?
stay-at-home
17
1
11

MONITOR
316
509
423
554
Grocery Distanced?
grocery-distanced
17
1
11

MONITOR
430
509
527
554
Schools Open?
schools-open
17
1
11

MONITOR
532
508
632
553
Transmission Prob
transmission-liklihood
2
1
11

MONITOR
11
401
198
446
Current Phase
current-phase
17
1
11

@#$#@#$#@
## WHAT IS IT?

A model for COVID-19

## HOW IT WORKS

(what rules the agents use to create the overall behavior of the model)

## HOW TO USE IT

(how to use the model, including a description of each of the items in the Interface tab)

## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

(suggested things to add or change in the Code tab to make the model more complicated, detailed, accurate, etc.)

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)

## RELATED MODELS

(models in the NetLogo Models Library and elsewhere which are of related interest)

## CREDITS AND REFERENCES

(a reference to the model's URL on the web if it has one, as well as any other necessary credits, citations, and links)
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.1.1
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
0
@#$#@#$#@
