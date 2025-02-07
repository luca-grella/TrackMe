<p align="center">
<img width="400" height="400" src="https://github.com/luca-grella/LunghiGrella/blob/master/logo/logo.png"><br><br>
Software Engineering 2 Project<br>
A.Y. 2018-2019<br>
Authors: Luca Grella & Daniele Lunghi<br>
Copyright © 2018<br>
All rights reserved
</p>
<br>

# The problem: TrackMe
TrackMe is a company that wants to develop a software-based service allowing third parties to monitor the location and health status of individuals. This service is called Data4Help. The service supports the registration of individuals who, by registering, agree that TrackMe acquires their data (data acquisition can happen through smartwatches or similar devices). Also, it supports the registration of third parties. After registration, these third parties can request:

• Access to the data of some specific individuals (we can assume, for instance, that they know an individual by his/her social security number or fiscal code in Italy). In this case, TrackMe passes the request to the specific individuals who can accept or refuse it.

• Access to anonymized data of groups of individuals (for instance, all those living in a certain geographical area, all those of a specific age range, etc.). These requests are handled directly by TrackMe that approves them if it is able to properly anonymize the requested data. For instance, if the third party is asking for data about 10-year-old children living in a certain street in Milano and the number of these children is two, then the third party could be able to derive their identity simply having people monitoring the residents of the street between 8.00 and 9.00 when kids go to school. Then, to avoid this risk and the possibility of a misuse of data, TrackMe will not accept the request. For simplicity, we assume that TrackMe will accept any request for which the number of individuals whose data satisfy the request is higher than 1000.

As soon as a request for data is approved, TrackMe makes the previously saved data available to the third party. Also, it allows the third party to subscribe to new data and to receive them as soon as they are produced.
Imagine now that, after some time, TrackMe realizes that a good part of its third-party customers wants to use the data acquired through Data4Help to offer a personalized and non-intrusive SOS service to elderly people. Therefore, TrackMe decides to build a new service, called AutomatedSOS, on top of Data4Help. AutomatedSOS monitors the health status of the subscribed customers and, when such parameters are below certain thresholds, sends to the location of the customer an ambulance, guaranteeing a reaction time of less than 5 seconds from the time the parameters are below the threshold.


## RASD

The Requirements analysis and specification document (RASD) contains the description of the scenarios, the use cases that describe them, and the models describing requirements and specification for the problem under consideration. You are to use a suitable mix of natural language, UML, and Alloy. UML and Alloy MUST be part of the documentation. You must also show that you used the Alloy tool for analysis, by reporting the models you obtained by using it. Of course, the initial written problem statement we provide suffers from the typical drawbacks of natural language descriptions: it is informal, incomplete, uses different terms for the same concepts, and the like. You may choose to solve the incompleteness and ambiguity as you wish, but be careful to clearly document the choices you make and the corresponding rationale. You will also include in the document information on the number of hours each group member has worked towards the fulfillment of this deadline. As a reference structure for your document, you should refer to the one reported below that is derived from the one suggested by IEEE.
Please include in the document information about the effort spent by each group member for completing this document.

[Our Requirements Analysis and Specification Document](https://github.com/luca-grella/LunghiGrella/blob/master/DeliveryFolder/RASD2.pdf)


## DD
The Design document (DD) must contain a functional description of the system, and any other view you find useful to provide. You should use all the UML diagrams you need to provide a full description of the system. Alloy may also be useful, although its use is not mandatory here. You will also include information on the number of hours each group member has worked towards the fulfillment of this deadline.

[Our Design Document](https://github.com/luca-grella/LunghiGrella/blob/master/DeliveryFolder/DD2.pdf)


## ALLOY 

[Code](https://github.com/luca-grella/LunghiGrella/blob/master/DeliveryFolder/Alloy.als)

[Model](https://github.com/luca-grella/LunghiGrella/blob/master/DeliveryFolder/Alloymodel.png)


## PRESENTATION

[PDF Version](https://github.com/luca-grella/LunghiGrella/blob/master/Presentation/SE2Presentation.pdf)

[KeyNote Version](https://github.com/luca-grella/LunghiGrella/blob/master/Presentation/SE2Presentation.key)

[PowerPoint Version](https://github.com/luca-grella/LunghiGrella/blob/master/Presentation/SE2Presentation.pptx)

[Older PowerPoint Version](https://github.com/luca-grella/LunghiGrella/blob/master/Presentation/SE2Presentation.ppt)
