# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                                         #
#   Copyright 2014 by Francisco Pinto <francisco.pinto@epfl.ch>           #
#                                                                         #
#   Center for Digital Education (CEDE)                                   #
#   Ecole Polytecnique Federale de Lausanne (EPFL)                        #
#   1015 Lausanne, Switzerland                                            #
#                                                                         #
#   This program is free software: you can redistribute it and/or modify  #
#   it under the terms of the GNU General Public License as published by  #
#   the Free Software Foundation, either version 3 of the License, or     #
#   (at your option) any later version.                                   #
#                                                                         #
#   This program is distributed in the hope that it will be useful,       #
#   but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#   GNU General Public License for more details.                          #
#                                                                         #
#   Visit the GNU General Public License website for more details:        #
#   http://www.gnu.org/licenses/                                          #
#                                                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


import re, gzip, progressbar, time, os, sys, pycountry, unicodedata, math
from ipaddress import IPv4Address
import simplejson as json
from jsonpath import jsonpath
import subprocess
import hashlib
from dateutil.parser import parse as iso2datetime
from pytz import timezone
from calendar import timegm
from datetime import datetime, timedelta
import pymongo
from termcolor import colored, cprint
import csv

import urllib2
from xml.dom.minidom import parseString
from lxml import etree
from random import randrange

import xmltodict
from xml.etree import ElementTree

# Path to IP database
IPTablePath = 'IPDB.csv'

# Event types dictionary
EventTypes = {

'Account' :
	{	'edx.course.enrollment.activated' 			: 'Account.Activate',
		'edx.course.enrollment.deactivated' 		: 'Account.Deactivate',
		'students_update_enrollment' 				: 'Account.InfoUpdate',
		'edx.course.enrollment.mode_changed' 		: 'Account.Upgrade',
		'edx.course.enrollment.upgrade.succeeded' 	: 'Account.Upgrade.Receipt',
		'accounts/login' 							: 'Account.Login'
	},
'Video' :
	{	'load_video' 				: 'Video.Load',
		'play_video' 				: 'Video.Play',
		'pause_video' 				: 'Video.Pause',
		'seek_video' 				: 'Video.Seek',
		'stop_video' 				: 'Video.Stop',
		'speed_change_video' 		: 'Video.SpeedChange',
		'show_transcript' 			: 'Video.Transcript.Show',
		'hide_transcript' 			: 'Video.Transcript.Hide',
		'transcript/download' 		: 'Video.Transcript.Download',
		'transcript/translation/en' : 'Video.Transcript.Translate.EN',
		'transcript/translation/fr' : 'Video.Transcript.Translate.FR',
		'transcript/translation' 	: 'Video.Transcript.Translate'
	},
'Problem' : 
	{	'problem_show' 			: 'Problem.Show',
		'problem_check' 		: 'Problem.Check',
		'problem_check_fail' 	: 'Problem.Check.Fail',
		'problem_graded' 		: 'Problem.Graded',
		'problem_save' 			: 'Problem.Save',
		'save_problem_fail' 	: 'Problem.Save.Fail',
		'save_problem_success' 	: 'Problem.Save.Success',
		'reset_problem' 		: 'Problem.Reset',
		'problem_reset' 		: 'Problem.Reset',
		'reset_problem_fail' 	: 'Problem.Reset.Fail'
	},
'Forum' :
	{	'comments/[^/]*/delete'									: 'Forum.Post.Delete', # Delete "post on thread" and "comment on post"
		'comments/[^/]*/flagAbuse'								: 'Forum.Post.Report',
		#'comments/[^/]*/reply'									: 'Forum.Post.CommentOn', # Comment on post
		'comments/[^/]*/unFlagAbuse'							: 'Forum.Post.Unreport',
		'comments/[^/]*/unvote'									: 'Forum.Post.Unvote',
		'comments/[^/]*/update'									: 'Forum.Post.Update',
		'comments/[^/]*/upvote'									: 'Forum.Post.Upvote',
		'forum'													: 'Forum.Load',
		'forum\)'												: 'Forum.Load',
		'forum/'												: 'Forum.Load',
		'forum/[^/]*/inline'									: 'Forum.Unknown',
		'forum/[^/]*/threads/[^/]*'								: 'Forum.Thread.View',
		#'forum/[^/]*/threads/create'							: 'Forum.Thread.Launch', # Thread launch
		'forum/i4x-edx-templates-course-Empty/inline'			: 'Forum.Unknown',
		'forum/i4x-edx-templates-course-Empty/threads/[^/]*'	: 'Forum.Unknown',
		'forum/i4x-EPFLx-[^-]*-course-[^/]*/threads/[^/]*'		: 'Forum.Thread.View',
		'forum/search'											: 'Forum.Search',
		'forum/undefined/threads/[^/]*'							: 'Forum.Thread.View',
		'forum/users/[^/]*'										: 'Forum.User.View',
		'i4x-edx-templates-course-Empty/threads/create'			: 'Forum.Thread.Launch',
		'threads/[^/]*/delete'									: 'Forum.Thread.Delete', # Delete lauched thread
		'threads/[^/]*/flagAbuse'								: 'Forum.Thread.Unreport',
		'threads/[^/]*/follow'									: 'Forum.Thread.Follow',
		'threads/[^/]*/pin'										: 'Forum.Thread.Pin',
		#'threads/[^/]*/reply'									: 'Forum.Thread.PostOn', # Post on thread
		'threads/[^/]*/unFlagAbuse'								: 'Forum.Thread.Report',
		'threads/[^/]*/unfollow'								: 'Forum.Thread.Unfollow',
		'threads/[^/]*/unvote'									: 'Forum.Thread.Unvote',
		'threads/[^/]*/update'									: 'Forum.Thread.Update',
		'threads/[^/]*/upvote'									: 'Forum.Thread.Upvote',
		'upload'												: 'Forum.Upload'
	}
}

#=========================================================#
#               GENERAL PURPOSE FUNCTIONS                 #
#=========================================================#

# Get current time
def ISO8601_utcnow():
	return datetime.utcnow().isoformat()+'+00:00'

# Time conversion: ISO8601 to POSIX
def ISO8601_to_POSIXtime(ISOTime):
	DTObj = iso2datetime(ISOTime).astimezone(timezone('UTC'))
	usec = DTObj.microsecond
	POSIXTimeInt = timegm(DTObj.timetuple())
	POSIXTime = float(str(POSIXTimeInt)+'.'+str(usec))
	return POSIXTime

# Time conversion: POSIX to ISO8601	
def POSIXtime_to_ISO8601(POSIXTime):
	ISOTime = datetime.utcfromtimestamp(POSIXTime).isoformat()+'+00:00'
	return ISOTime
	
# Pretty-print JSON
def printjson(s, Color='grey'):
	cprint(json.dumps(s, sort_keys=True, indent=4, separators=(',', ': ')), Color)

# Generate unique FileID
def GenerateFileID(RelativePath):
	FileID = hashlib.md5()
	FileID.update(str(RelativePath))
	return FileID.hexdigest()

# Generate unique EventID	
def GenerateEventID(CourseID, StudentID, ISOTime, EventType):
	EventID = hashlib.md5()
	EventID.update(str(CourseID)+str(StudentID)+str(ISOTime)+str(EventType))
	return EventID.hexdigest()
	
# Save event list as JSON file
def SaveListToJSON(ItemList, JSONFilePath):
	try:
		f = gzip.open(JSONFilePath, 'w')
		for Item in ItemList:
			JSONString = json.dumps(Item)
			f.write("%s\n" % JSONString)
		f.close()
		cprint('[Clean JSON] [Success] File saved: %s' % JSONFilePath, 'green')
		return True
	except:
		cprint('[Clean JSON] [Success] File saved: %s' % JSONFilePath, 'red')
		exit()

# Impor CSV-type file into JSON list
def ImportCSVFile(FilePath):
	
	f = open(FilePath, 'r')
	Body = f.read().replace('\t','|')
	f.close()
	
	while True:
		if '||' in Body:
			Body = Body.replace('||','|NULL|')
		else:
			break
			
	Body = Body.replace('\n\r\\n',' ')
	Body = Body.replace('\r\n\\n',' ')
	Body = Body.replace('\n\\n',' ')
	Body = Body.replace('\r\\n',' ')
	
	CSVTable = csv.reader(Body.splitlines(), delimiter='|')
	CSVList = list(CSVTable)
	
	Keys = CSVList[0]
	Rows = CSVList[1:]
	
	JSONList = []
	for row in Rows:
		JSONList.append( json.dumps(dict(zip(Keys,row))) )
	
	return JSONList
	
# END DEF ImportCSVFile ----------

#=========================================================#
#           GENERAL JSON HANDLING FUNCTIONS               #
#=========================================================#

def IsAttribute(JSON, AttributePath):	
	
	if len(AttributePath)==1:
		if jsonpath(JSON, AttributePath):
			return True
		else:
			return False
	else:
		for Path in AttributePath:
			if not jsonpath(JSON, Path):
				return False
		return True

def GetAttribute(JSON, AttributePath, IgnoreErrors=False):
	
	Attribute = jsonpath(JSON, AttributePath)
	
	if Attribute:
		if len(Attribute)==1:
			return Attribute[0]
		else:
			if IgnoreErrors:
				cprint('[WARNING] GetAttribute() - Error reading attribute: "%s". Returned "null".' % AttributePath, 'magenta')
				return None
			else:
				printjson(JSON, 'red')
				cprint('[ERROR] GetAttribute() - Error reading attribute: "%s".' % AttributePath, 'red')
				exit()
	else:
		if IgnoreErrors:
			cprint('[WARNING] GetAttribute() - Attribute not found: "%s". Returned "null".' % AttributePath, 'magenta')
			return None
		else:
			printjson(JSON, 'red')
			cprint('[ERROR] GetAttribute() - Attribute not found: "%s".' % AttributePath, 'red')
			exit()
		
#=========================================================#
#         ERROR, WARNING, AND SUCCESS MESSAGES            #
#=========================================================#

def Warning_MissingAttribute(ItemClass, AttributeName):
	cprint('[Edx Log] [%s Data] [Warning] Attribute unexpectedly missing in EdX log item: %s. Replaced with "null".' % (ItemClass, AttributeName), 'magenta')



		

#=========================================================#
#           GENERAL EVENT PARSING FUNCTIONS               #
#=========================================================#

# Parse Edx .log file, and save into CEDE .json file if it doesn't exist yet
# This is the main function in this library, and ideally the only one that needs to be called
def ParseAndSave(LOGFilePath, JSONFilePath, ItemClass, Locate=False, KeepAlive=False):
	
	# Check if .json file exists
	if not os.path.isfile(JSONFilePath):
		# If not, parse file and save
		Output = ParseAndReplace(LOGFilePath, JSONFilePath, ItemClass, Locate, KeepAlive)
		return Output
	else:
		# If yes, return and print "File exists" message
		cprint('[EdX Log] [%s Data] [Warning] File already exists. To overwrite, use pyedx.ParseAndReplace()\n%s' % (ItemClass, JSONFilePath), 'yellow')
		return False

# Parse Edx .log file, and save into CEDE .json file
def ParseAndReplace(LOGFilePath, JSONFilePath, ItemClass, Locate=False, KeepAlive=False):
	
	# Parse and save "mouse click", "forum activity", and "course sign up" event types
	if ItemClass in ['Click', 'Forum', 'SignUp']:
		ItemList = ParseEventFile(LOGFilePath, ItemClass)
	# Parse and save "student IP/location" info
	elif ItemClass=='StudentIP':
		ItemList = ParseStudentIPFile(LOGFilePath, Locate)
	# Parse and save "video" info
	elif ItemClass=='Video':
		ItemList = ParseVideoFile(LOGFilePath, KeepAlive)
	# Parse and save "video" info
	elif ItemClass=='Problem':
		ItemList = ParseProblemFile(LOGFilePath)
	# Return if item class is invalid
	else:
		cprint('[EdX Log] [Error] ParseAndReplace() - Unknown item class: %s' % ItemClass, 'red')
		exit()
	
	# Save to JSON file if list is not empty
	SaveListToJSON(ItemList, JSONFilePath)
	if len(ItemList)>0:
		return True
	# Return with warning if list is empty
	else:
		cprint('[EdX Log] [%s Data] [Warning] Parsing function returned empty JSON item list. An empty file was saved.' % ItemClass, 'magenta')
		return True
		
# END DEF ParseAndReplace ----------

# Load FILE with events (.log/.json/.mongo) and return list of JSON items
def LoadEventFile(FilePath):

	# Load compressed file of type .log.gz
	if FilePath.endswith('.log.gz') or FilePath.endswith('.json.gz'):
		f = gzip.open(FilePath, 'rb')
	# Load uncompressed file of type .log, .json, or .mongo
	elif FilePath.endswith('.log') or FilePath.endswith('.json') or FilePath.endswith('.mongo'):
		f = open(FilePath,'r')
	# Read JSON item strings and return as list
	JSONList = f.readlines()
	f.close()
	return JSONList
	
# Print FILE with events
def PrintEventFile(FilePath):
	JSONList = LoadEventFile(FilePath)
	for l in JSONList:
		printjson(json.loads(l))

# Parse FILE with events and return JSON event list
def ParseEventFile(FilePath, ItemClass):
	
	# Print to shell: Path of file being parsed
	cprint('[EdX Log] [%s Data] [Parsing...] EdX Log --> Clean JSON\n%s' % (ItemClass, FilePath), 'green', 'on_blue')
	
	# Get current time (for calculating processing time)
	StartTime = time.time()
	
	# Load compressed file of type .log.gz
	if FilePath.endswith('.log.gz'):
		f = gzip.open(FilePath, 'rb')
		JSONList = f.readlines()
		f.close()
	# Load uncompressed file of type .log or .mongo
	elif FilePath.endswith('.log') or FilePath.endswith('.mongo'):
		f = open(FilePath,'r')
		JSONList = f.readlines()
		f.close()
	# Load table of type .sql or .csv and convert to JSON
	elif FilePath.endswith('.sql') or FilePath.endswith('.csv'):
		JSONList = ImportCSVFile(FilePath)
	
	# Parse ugly edx log into clean JSON list
	CleanJSONList = ParseEventList(JSONList, ItemClass)
	
	# Print to shell: Number of events parsed and elapsed time
	print('[EdX Log] [%s Data] [Done parsing file] %s event(s) parsed. Elapsed time: %s seconds.' % (ItemClass, len(CleanJSONList), int(round(time.time() - StartTime))))
	
	# Return clean JSON list
	return CleanJSONList
	
# END DEF ParseEventFile ----------

# Parse LIST of events and return a clean JSON list
def ParseEventList(JSONList, EventClass):

	# Return empty list if len=0
	if len(JSONList)==0:
		return []
		
	# Create progress bar
	N = len(JSONList)
	PBar = progressbar.ProgressBar(maxval=N, term_width=50, widgets=[progressbar.Bar('=', '[', ']'), ' ', progressbar.Percentage()])
	PCounter = 0
	
	# Loop through list of events
	CleanJSONList = []
	for JSONString in JSONList:
		
		# Update progress bar
		if PCounter<=N:
			PBar.update(PCounter)
		PCounter += 1
	
		# Parse single "mouse click" event
		if EventClass=='Click':
			JSONItem = json.loads(JSONString)
			Event = ParseClickEvent(JSONItem)
		# Parse single "forum activity" event
		elif EventClass=='Forum':
			JSONItem = json.loads(JSONString)
			Event = ParseForumEvent(JSONItem)
		# Parse single "course sign up" event
		elif EventClass=='SignUp':
			JSONItem = json.loads(JSONString)
			Event = ParseSignUpEvent(JSONItem)
			
		# If event was parsed successfully, add to event list
		if Event:
			CleanJSONList.append(Event)
	
	# Close progress bar
	PBar.update(N)
	PBar.finish()
	
	# Return clean JSON list
	return CleanJSONList
	
# END DEF ParseEventList ----------
	
	
#=========================================================
# CLICKSTREAM EVENT PARSING FUNCTIONS
#=========================================================

# Parse SINGLE Click Event [Depth 2]
def ParseClickEvent(JSONItem):

	# Get event type
	event_type = JSONItem['event_type']
	
	# Initialize variables
	EventMetadata = {}
	Event = {}
	CourseID = []
	StudentID = []
	ISOTime = []
	EventType = []
	EventID = []
	
	#=========================#
	#   User Account Events   #
	#=========================#
	if 'enrollment' in event_type or 'login' in event_type:
	
		# Parse event type out of event_type field
		MatchedType = re.findall(r'(edx.course.enrollment.activated|students_update_enrollment|edx.course.enrollment.deactivated|edx.course.enrollment.mode_changed|edx.course.enrollment.upgrade.succeeded|accounts/login)', event_type)
		
		# Found meaningful event type?
		if len(MatchedType)==0: # NO
			return False
			
		else: # YES
		
			# Try to get integer student ID. Return if failed
			if not 'user_id' in JSONItem['context'] and not 'user_id' in JSONItem['event']:
				return False
			elif 'user_id' in JSONItem['context'] and not 'user_id' in JSONItem['event']:
				StudentID = JSONItem['context']['user_id']
			elif not 'user_id' in JSONItem['context'] and 'user_id' in JSONItem['event']:
				StudentID = JSONItem['event']['user_id']
			elif 'user_id' in JSONItem['context'] and 'user_id' in JSONItem['event']:
				if JSONItem['context']['user_id']==JSONItem['event']['user_id']:
					StudentID = JSONItem['context']['user_id']
				else:
					return False
			else:
				return False
			if not isinstance(StudentID, int):
				return
		
			# Get rest of basic event data
			CourseID = JSONItem['context']['course_id'].replace('/','-')
			ISOTime = JSONItem['time']
			POSIXTime = ISO8601_to_POSIXtime(ISOTime)
			EventType = EventTypes['Account'][MatchedType[0]]
			EventID = GenerateEventID(CourseID, StudentID, ISOTime, EventType)
			
			# Build basic event matadata dict
			EventMetadata = {'EventID' : EventID, 'EdxEventTag' : MatchedType[0]}
			
			# Build event dict
			Event = {'StudentID' : StudentID, 'TimeStamp' : {'ISO8601' : ISOTime, 'POSIX' : POSIXTime}, 'EventType' : EventType, 'EventID' : EventID, 'EventMetadata' : EventMetadata}
			
			# Build course event dict
			CourseEvent = {'CourseID' : CourseID, 'Event': Event}
			
			# Return course event dict			
			return CourseEvent
			
		# END ELSE ----------
	
	# END IF ----------
	
	
	#==============================#
	#   Video Interaction Events   #
	#==============================#
	elif 'video' in event_type or 'transcript' in event_type:
		
		# Parse event type out of event_type field
		MatchedType = re.findall(r'(load_video|play_video|pause_video|seek_video|stop_video|speed_change_video|show_transcript|hide_transcript|transcript/download|transcript/translation/en|transcript/translation/fr|transcript/translation)', event_type)
		
		# Found meaningful event type?
		if len(MatchedType)==0: # NO
			return False
			
		# Basic event data available?
		if not IsAttribute(JSONItem, ['context.course_id', 'context.user_id', 'time']): # NO
		   return False
			
		else: # YES
		
			# Get basic event data
			CourseID = GetAttribute(JSONItem, 'context.course_id').replace('/','-')
			StudentID = GetAttribute(JSONItem, 'context.user_id')
			ISOTime = GetAttribute(JSONItem, 'time')
			POSIXTime = ISO8601_to_POSIXtime(ISOTime)
			EventType = EventTypes['Video'][MatchedType[0]]
			EventID = GenerateEventID(CourseID, StudentID, ISOTime, EventType)
			
			# Parse video ID out of event_type field
			MatchedID = re.findall(r'([a-z0-9]{32})', event_type)
			if len(MatchedID)>0:
				VideoID = MatchedID[0]
			else:
				MatchedID = re.findall(r'([a-z0-9]{32})', json.dumps(JSONItem['event']))	
				if len(MatchedID)>0:
					VideoID = MatchedID[0]
			
			# Return if failed to get video ID	
			if 'VideoID' not in locals():
				return False
			
			#----------------------
			# Event metadata fields
			#----------------------
			
			# Initialize variables
			CurrentTime = None
			OldTime = None
			NewTime = None
			SeekType = None
			OldSpeed = None
			NewSpeed = None
			
			# Re-parse event attribute
			JSONItem_Event = json.loads(GetAttribute(JSONItem, 'event'))
			
			# Get current time in video player
			if MatchedType[0] in ['play_video', 'pause_video', 'stop_video', 'show_transcript', 'hide_transcript']:
				CurrentTime = GetAttribute(JSONItem_Event, 'currentTime', IgnoreErrors=True)
				
			# Get old and new time when student navigates video player
			elif MatchedType[0]=='seek_video':
				OldTime = GetAttribute(JSONItem_Event, 'old_time', IgnoreErrors=True)
				NewTime = GetAttribute(JSONItem_Event, 'new_time', IgnoreErrors=True)
				SeekType = GetAttribute(JSONItem_Event, 'type', IgnoreErrors=True)
				
			# Get old and new speed when student changes video speed
			elif MatchedType[0]=='speed_change_video':
				OldSpeed = GetAttribute(JSONItem_Event, 'old_speed', IgnoreErrors=True)
				NewSpeed = GetAttribute(JSONItem_Event, 'new_speed', IgnoreErrors=True)
				
			# Build basic event matadata dict
			EventMetadata = {'EventID' : EventID, 'ParentVideoID' : VideoID, 'DepthInHierarchy' : 1, 'EdxEventTag' : MatchedType[0], 'CurrentTime' : CurrentTime, 'OldTime' : OldTime, 'NewTime' : NewTime, 'SeekType' : SeekType, 'OldSpeed' : OldSpeed, 'NewSpeed' : NewSpeed}
			
			# Build event dict
			Event = {'StudentID' : StudentID, 'TimeStamp' : {'ISO8601' : ISOTime, 'POSIX' : POSIXTime}, 'EventType' : EventType, 'EventID' : EventID, 'EventMetadata' : EventMetadata}
			
			# Build course event dict
			CourseEvent = {'CourseID' : CourseID, 'Event': Event}
		
			# Return course event dict			
			return CourseEvent
		
		# END ELSE ----------
		
	# END ELIF ----------
		
	#============================#
	#   Problem Solving Events   #
	#============================#
	elif 'problem' in event_type:
		
		# Parse event type out of event_type field
		MatchedType = re.findall(r'(problem_check|problem_check_fail|problem_graded|problem_reset|problem_save|problem_show|reset_problem|reset_problem_fail|save_problem_fail|save_problem_success)', event_type)
		
		# Found meaningful event type?
		if len(MatchedType)==0: # NO
			return False
			
		# Basic event data available?
		if not IsAttribute(JSONItem, ['context.course_id', 'context.user_id', 'time']): # NO
		   return False
		
		else: # YES
		
			# Get basic event data
			CourseID = JSONItem['context']['course_id'].replace('/','-')
			StudentID = JSONItem['context']['user_id']
			ISOTime = JSONItem['time']
			POSIXTime = ISO8601_to_POSIXtime(ISOTime)
			EventType = EventTypes['Problem'][MatchedType[0]]
			EventID = GenerateEventID(CourseID, StudentID, ISOTime, EventType)
			
			# Parse problem ID out of event_type field
			MatchedID = re.findall(r'([a-z0-9]{32})', event_type)
			if len(MatchedID)>0:
				ProblemID = MatchedID[0]
			else:
				MatchedID = re.findall(r'([a-z0-9]{32})', json.dumps(JSONItem['event']))	
				if len(MatchedID)>0:
					ProblemID = MatchedID[0]
					
			# Return if failed to get problem ID
			if 'ProblemID' not in locals():
				return False
				
			# Build basic event matadata dict
			EventMetadata = {'EventID' : EventID, 'ParentProblemID' : ProblemID, 'DepthInHierarchy' : 1, 'EdxEventTag' : MatchedType[0]}
			
			#---------------------------
			# "Problem Check" event type
			#---------------------------
			if MatchedType[0]=='problem_check':
			
				# Return if no answer and submission information available
				if not 'module' in JSONItem['context'].keys() or not 'submission' in JSONItem['event'].keys():
					return False
					
				#------------------------
				# Problem metadata fields
				#------------------------
				
				# Get problem display name
				DisplayName = JSONItem['context']['module']['display_name']
				
				# Get problem maximum grade
				if 'max_grade' in JSONItem['event'].keys():
					MaxGrade = JSONItem['event']['max_grade']
				else:
					MaxGrade = None
					
				# Build problem metadata dict
				ProblemMetadata = {'ProblemID' : ProblemID, 'DepthInHierarchy' : 0, 'DisplayName' : DisplayName, 'MaxGrade' : MaxGrade}
				
				#----------------------
				# Event metadata fields
				#----------------------
				
				# Get problem part IDs
				ProblemPartIDs = JSONItem['event']['submission'].keys()
				
				# Get more data if available
				if len(ProblemPartIDs)>0:
				
					# Initialize submissions list
					Submissions = []
					
					# Get all sub-submisions for problem
					for ProblemPartID in ProblemPartIDs:
						
						# Build answers dict, with index and text of student's answer
						AnswersText = JSONItem['event']['submission'][ProblemPartID]['answer']
						AnswersIndex = JSONItem['event']['answers'][ProblemPartID]
						Answers = {'Index' : AnswersIndex, 'Text' : AnswersText}
						
						# Get rest of part submission data
						Correct = JSONItem['event']['submission'][ProblemPartID]['correct']
						InputType = JSONItem['event']['submission'][ProblemPartID]['input_type']
						Question = JSONItem['event']['submission'][ProblemPartID]['question']
						ResponseType = JSONItem['event']['submission'][ProblemPartID]['response_type']
						Variant = JSONItem['event']['submission'][ProblemPartID]['variant']
						
						# Build part submission dict
						PartSubmission = {'Answers' : Answers, 'Correct' : Correct, 'InputType' : InputType, 'Question' : Question, 'ResponseType' : ResponseType, 'Variant' : Variant}
						
						# Add to submissions data list
						Submissions.append(PartSubmission)
				else:
					Submissions = None
				
				# Get number of attempts used by student to give right answer
				NumberOfAttempts = JSONItem['event']['attempts']
				
				# Get final grade for problem
				Grade = JSONItem['event']['grade']
				
				# Get correct/incorrect decision flag
				Success = JSONItem['event']['success']
				
				# Update event metada dict
				EventMetadata.update( {'Submissions' : Submissions, 'NumberOfAttempts' : NumberOfAttempts, 'Grade' : Grade, 'Success' : Success, 'ProblemMetadata' : ProblemMetadata} )
			
			# END IF ----------
			
			# Build event dict
			Event = {'StudentID' : StudentID, 'TimeStamp' : {'ISO8601' : ISOTime, 'POSIX' : POSIXTime}, 'EventType' : EventType, 'EventID' : EventID, 'EventMetadata' : EventMetadata}
			
			# Build course event dict
			CourseEvent = {'CourseID' : CourseID, 'Event': Event}
			
			#if (MatchedType[0]=='problem_check') and ('EPFLx/CS305/2014' in CourseID) and POSIXTime>1414764000.000 and POSIXTime<1414778400.000:
				#printjson(CourseEvent)
				#print '\n\n\n\n\n\n\n\n\n'
				
			# Return course event dict
			return CourseEvent
			
		# END ELSE ----------
		
	# END ELIF ----------
	
	#===========================#
	#   Forum Activity Events   #
	#===========================#
	elif 'discussion' in event_type or 'forum' in event_type:
		
		# Parse event type out of event_type field
		MatchedType = re.findall(r'(comments/[^/]*/delete$|comments/[^/]*/flagAbuse$|comments/[^/]*/reply$|comments/[^/]*/unFlagAbuse$|comments/[^/]*/unvote$|comments/[^/]*/update$|comments/[^/]*/upvote$|forum$|forum\)$|forum/$|forum/[^/]*/inline$|forum/[^/]*/threads/[^/]*$|forum/[^/]*/threads/create$|forum/i4x-edx-templates-course-Empty/inline$|forum/i4x-edx-templates-course-Empty/threads/[^/]*$|forum/i4x-EPFLx-[^\-]*-course-[^/]*/threads/[^/]*$|forum/search$|forum/undefined/threads/[^/]*$|forum/users/[^/]*$|i4x-edx-templates-course-Empty/threads/create$|threads/[^/]*/delete$|threads/[^/]*/flagAbuse$|threads/[^/]*/follow$|threads/[^/]*/pin$|threads/[^/]*/reply$|threads/[^/]*/unFlagAbuse$|threads/[^/]*/unfollow$|threads/[^/]*/unvote$|threads/[^/]*/update$|threads/[^/]*/upvote$|upload)', event_type)
		
		# Found meaningful event type?
		if len(MatchedType)==0: # NO
			return False
			
		# Basic event data available?
		if not IsAttribute(JSONItem, ['context.course_id', 'context.user_id', 'time']): # NO
		   return False
			
		else: # YES
			
			# Strip out forum/thread/comment ID from event type
			NoIDType = MatchedType[0]
			for match in re.findall(r'([a-z0-9]{32})', NoIDType):
				NoIDType = NoIDType.replace(match, '[^/]*')
			for match in re.findall(r'([a-z0-9]{24})', NoIDType):
				NoIDType = NoIDType.replace(match, '[^/]*')
			for match in re.findall(r'([0-9]{2,10}$)', NoIDType):
				NoIDType = NoIDType.replace(match, '[^/]*')
			for match in re.findall(r'(forum/[^/]*/threads/)', NoIDType):
				NoIDType = NoIDType.replace(match, 'forum/[^/]*/threads/')
			for match in re.findall(r'(forum/[^/]*/inline)', NoIDType):
				NoIDType = NoIDType.replace(match, 'forum/[^/]*/inline')
			
			# Get basic event data
			CourseID = JSONItem['context']['course_id'].replace('/','-')
			StudentID = JSONItem['context']['user_id']
			ISOTime = JSONItem['time']
			POSIXTime = ISO8601_to_POSIXtime(ISOTime)
			if NoIDType in EventTypes['Forum'].keys():
				EventType = EventTypes['Forum'][NoIDType]
			else:
				return False
			EventID = GenerateEventID(CourseID, StudentID, ISOTime, EventType)
			
			# Try to get IDs and build event matadata dict. Return if failed
			if 'Forum.Thread' in EventType:
				Match = re.findall(r'([a-z0-9]{24})', MatchedType[0])
				if len(Match)==0:
					return False
				ThreadID = Match[0]
				EventMetadata = {'EventID' : EventID, 'ParentThreadID' : ThreadID, 'DepthInHierarchy' : 2, 'EdxEventTag' : MatchedType[0]}
			elif 'Forum.Post' in EventType:
				Match = re.findall(r'([a-z0-9]{24})', MatchedType[0])
				if len(Match)==0:
					return False
				PostID = Match[0]
				EventMetadata = {'EventID' : EventID, 'ParentPostID' : PostID, 'DepthInHierarchy' : 3, 'EdxEventTag' : MatchedType[0]}			
			else:
				EventMetadata = {'EventID' : EventID, 'ParentForumID' : None, 'DepthInHierarchy' : 1, 'EdxEventTag' : MatchedType[0]}
			
			# Build event dict
			Event = {'StudentID' : StudentID, 'TimeStamp' : {'ISO8601' : ISOTime, 'POSIX' : POSIXTime}, 'EventType' : EventType, 'EventID' : EventID, 'EventMetadata' : EventMetadata}
			
			# Build course event dict
			CourseEvent = {'CourseID' : CourseID, 'Event': Event}
		
			# Return course event dict
			return CourseEvent
			
		# END ELSE ----------
	
	# END ELIF ----------

	#=================================#
	#   Non-Meaningful Click Events   #
	#=================================#
	
	else:
		return False
		
# END DEF ParseClickEvent ----------

#=========================================================
# FORUM EVENT PARSING FUNCTIONS
#=========================================================

def ParseForumEvent(JSONItem):
	
	#------------------
	# Get common fields
	#------------------
	AbuseFlaggers = JSONItem['abuse_flaggers']
	Anonymous = JSONItem['anonymous']
	AnonymousToPeers = JSONItem['anonymous_to_peers']
	AtPositionList = JSONItem['at_position_list']
	StudentID = JSONItem['author_id']
	AuthorUsername = JSONItem['author_username']
	Body = JSONItem['body']
	CourseID = JSONItem['course_id'].replace('/','-')
	CreatedAt = JSONItem['created_at']['$date']
	HistoricalAbuseFlaggers = JSONItem['historical_abuse_flaggers']
	Visible = JSONItem['visible']
	Votes = JSONItem['votes']
	UpdatedAt = JSONItem['updated_at']['$date']
	
	CreatedAt_POSIXTime = float(CreatedAt)/1000
	CreatedAt_ISOTime = POSIXtime_to_ISO8601(CreatedAt_POSIXTime)
	CreatedAt = {'ISO8601' : CreatedAt_ISOTime, 'POSIX' : CreatedAt_POSIXTime}
	
	UpdatedAt_POSIXTime = float(UpdatedAt)/1000
	UpdatedAt_ISOTime = POSIXtime_to_ISO8601(UpdatedAt_POSIXTime)
	UpdatedAt = {'ISO8601' : UpdatedAt_ISOTime, 'POSIX' : UpdatedAt_POSIXTime}
	
	VotesCount = JSONItem['votes']['count']
	VotesPoint = JSONItem['votes']['point']
	VotesDownCount  = JSONItem['votes']['down_count']
	VotesUp = JSONItem['votes']['up']
	VotesDown = JSONItem['votes']['down']
	VotesUpCount = JSONItem['votes']['up_count']
	
	Votes = {
		'Count': VotesCount,
		'UpVotes' : {'Count' : VotesUpCount, 'StudentIDs' : VotesUp},
		'DownVotes' : {'Count' : VotesDownCount, 'StudentIDs' : VotesDown},
		'Score': VotesPoint,
	}
	
	# Create common item metadata
	CommonItemMetadata = {'AbuseFlaggers' : AbuseFlaggers, 'Anonymous' : Anonymous, 'AnonymousToPeers' : AnonymousToPeers, 'AtPositionList' : AtPositionList, 'Text' : Body, 'HistoricalAbuseFlaggers' : HistoricalAbuseFlaggers, 'Visible' : Visible, 'Votes' : Votes, 'UpdatedAt' : UpdatedAt, 'Votes' : Votes}
	
	# Get common fields	
	ID = JSONItem['_id']['$oid']
	Type = JSONItem['_type']
	
	# Get SK field (this determines if event relates to thread, post, or comment)
	if 'sk' in JSONItem.keys():
		SK = JSONItem['sk']
	else:
		SK = False
	
	
	#----------------------
	# Thread launch events
	#----------------------
	if SK==False:
	
		EventType = 'Forum.Thread.Launch'
		EventID = GenerateEventID(CourseID, StudentID, CreatedAt_ISOTime, EventType)
		ItemType = 'Thread'
		ThreadID = ID
		
		# Add type-specific fields to common metadata
		Closed = JSONItem['closed']
		CommentCount = JSONItem['comment_count']
		CommentableID = JSONItem['commentable_id']
		LastActivityAt = JSONItem['last_activity_at']['$date']
		LastActivityAt_POSIXTime = float(LastActivityAt)/1000
		LastActivityAt_ISOTime = POSIXtime_to_ISO8601(LastActivityAt_POSIXTime)
		LastActivityAt = {'ISO8601' : LastActivityAt_ISOTime, 'POSIX' : LastActivityAt_POSIXTime}
		if 'pinned' in JSONItem.keys():
			Pinned = JSONItem['pinned']
		else:
			Pinned = None
		if 'tags_array' in JSONItem.keys():
			TagsArray = JSONItem['tags_array']
		else:
			TagsArray = None
		if 'thread_type' in JSONItem.keys():	
			ThreadType = JSONItem['thread_type']
		else:
			ThreadType = None
		Title = JSONItem['title']
		CommonItemMetadata.update({'Closed' : Closed, 'CommentCount' : CommentCount, 'CommentableID' : CommentableID, 'LastActivityAt' : LastActivityAt, 'Pinned' : Pinned, 'TagsArray' : TagsArray, 'ThreadType' : ThreadType})
		
		# Build Event Metadata JSON
		EventMetadata = {
			'EventID' : EventID,
			'ParentThreadID' : ThreadID,
			'DepthInHierarchy' : 2,
			'EdxEventTag' : Type,
			'ThreadMetadata' :
			{
				'ItemType' : ItemType,
				'ThreadID' : ThreadID,
				'ParentForumID' : None,
				'DepthInHierarchy' : 1,
			}	
		}
		EventMetadata['ThreadMetadata'].update(CommonItemMetadata)
		
	# END IF ----------	
		
	#-----------------------
	# Post on thread events
	#-----------------------	
	elif len(SK)==24:
		
		EventType = 'Forum.Thread.PostOn'
		EventID = GenerateEventID(CourseID, StudentID, CreatedAt_ISOTime, EventType)
		ItemType = 'Post'
		PostID = ID
		ParentThreadID = JSONItem['comment_thread_id']['$oid']
		
		# Add type-specific fields to common metadata
		Endorsed = JSONItem['endorsed']
		CommonItemMetadata.update({'Endorsed' : Endorsed})
		
		# Build Event Metadata JSON
		EventMetadata = {
			'EventID' : EventID,
			'ParentPostID' : PostID,
			'DepthInHierarchy' : 3,
			'EdxEventTag' : Type,
			'PostMetadata' :
			{
				'ItemType' : ItemType,
				'PostID' : PostID,
				'ParentThreadID' : ParentThreadID,
				'DepthInHierarchy' : 2,
				
			}	
		}
		EventMetadata['PostMetadata'].update(CommonItemMetadata)
		
	# END ELIF ----------	
					
	#------------------------
	# Comment on post events
	#------------------------	
	elif len(SK)==49:
		
		EventType = 'Forum.Post.CommentOn'
		EventID = GenerateEventID(CourseID, StudentID, CreatedAt_ISOTime, EventType)
		ItemType = 'Comment'
		CommentID = ID
		ParentPostID = JSONItem['parent_id']['$oid']
		ParentThreadID = JSONItem['comment_thread_id']['$oid']
		
		# Add type-specific fields to common metadata
		Endorsed = JSONItem['endorsed']
		CommonItemMetadata.update({'Endorsed' : Endorsed})
		
		# Build Event Metadata JSON
		EventMetadata = {
			'EventID' : EventID,
			'ParentCommentID' : CommentID,
			'DepthInHierarchy' : 4,
			'EdxEventTag' : Type,
			'CommentMetadata' :
			{
				'ItemType' : ItemType,
				'CommentID' : CommentID,
				'ParentPostID' : ParentPostID,
				'DepthInHierarchy' : 3,
				'ParentThreadID' : ParentThreadID,
				'Endorsed' : Endorsed
			}	
		}
		EventMetadata['CommentMetadata'].update(CommonItemMetadata)
		
	# END ELIF ----------
	
	# Build event dict
	Event = {'StudentID' : StudentID, 'TimeStamp' : CreatedAt, 'EventType' : EventType, 'EventID' : EventID, 'EventMetadata' : EventMetadata}
	
	# Build course event dict
	CourseEvent = {'CourseID' : CourseID, 'Event': Event}
	
	# Return course event dict
	return CourseEvent

# END DEF ParseForumEvent ----------

#=========================================================
# STUDENT SIGN-UP PARSING FUNCTIONS
#=========================================================

def ParseSignUpEvent(JSONItem):
	
	#-------------------
	# Get common fields
	#-------------------
	CourseID = JSONItem['course_id'].replace('/','-')
	StudentID = JSONItem['user_id']
	CreatedAt = JSONItem['created']+' UTC'
	IsActive = JSONItem['is_active']
	Mode = JSONItem['mode']
	EdxSignUpCounter = JSONItem['id']
	
	CreatedAt_POSIXTime = ISO8601_to_POSIXtime(CreatedAt)
	CreatedAt_ISOTime = POSIXtime_to_ISO8601(CreatedAt_POSIXTime)
	TimeStamp = {'ISO8601' : CreatedAt_ISOTime, 'POSIX' : CreatedAt_POSIXTime}
	
	EventType = 'Course.SignUp'
	EventID = GenerateEventID(CourseID, StudentID, CreatedAt_ISOTime, EventType)
	
	# Build Event Metadata JSON
	EventMetadata = {
		'EventID' : EventID,
		'IsActive' : IsActive,
		'Mode' : Mode,
		'EdxSignUpCounter' : EdxSignUpCounter
	}

	#------------------
	# Build JSON event 
	#------------------
	Event = {'StudentID' : StudentID, 'TimeStamp' : TimeStamp, 'EventType' : EventType, 'EventID' : EventID, 'EventMetadata' : EventMetadata}
	CourseEvent = {'CourseID' : CourseID, 'Event': Event}
	
	# Return JSON event
	return CourseEvent




#=========================================================
# STUDENT IP PARSING FUNCTIONS
#=========================================================

def ParseStudentIPFile(FilePath, Locate=False):

	cprint('[EdX Log] [IP Lookup] [Parsing...] EdX Log --> Clean JSON\n%s' % FilePath, 'green', 'on_blue')
	StartTime = time.time()
	
	ItemList = []
	JSONList = LoadEventFile(FilePath)
	
	for l in JSONList:
		
		JSON = json.loads(l)
		
		try:
			NewItem = [JSON['context']['user_id'], JSON['username'], JSON['ip']]
			if not NewItem in ItemList:
				ItemList.append(NewItem)
		except:
			pass
	
	JSONListClean = ParseStudentIPList(ItemList, Locate)
	#print 'Exiting without saving'
	#exit()
	print('\r[EdX Log] [IP Lookup] [Done parsing file] %s item(s) parsed. Elapsed time: %s seconds.' % (len(ItemList), int(round(time.time() - StartTime))))
	
	return JSONListClean
	


def ParseStudentIPList(ItemList, Locate=False):

	JSONListClean = []
	
	# Counter
	N = len(ItemList)
	
	if N>0:
		#PBar = progressbar.ProgressBar(maxval=N, term_width=50, widgets=[progressbar.Bar('=', '[', ']'), ' ', progressbar.Percentage()])
		PCounter = 0
	
		for Item in sorted(ItemList):
		
			JSONCleanItem = ParseStudentIPItem(Item, Locate)
			
			# Update progress bar
			#if PCounter<=N:
			#	PBar.update(PCounter)
			PCounter += 1
			
			if Locate:
				if JSONCleanItem['Location']:
					PercentageStr = '['+str(int(round(float(PCounter)/float(N)*100)))+'%] '
					MSG = PercentageStr+colored('IP located: %s --> %s, %s' % (JSONCleanItem['IP'], JSONCleanItem['Location']['City'], JSONCleanItem['Location']['Country']['Name']), 'green')
					MSG = str.ljust(MSG, 100)
					sys.stdout.write('\r'+MSG+' '*len(PercentageStr))
					sys.stdout.flush()
				else:
					cprint('[ERROR] ParseStudentIPList() - IP not found in database: %s' % Item[2], 'red')
					exit()
					
			
					
			JSONListClean.append(JSONCleanItem)
		
		# Close progress bar
		#PBar.update(N)
		#PBar.finish()
	

		
	return JSONListClean
	

def ParseStudentIPItem(Item, Locate=False):
	
	# Initialize output JSON item
	JSONClean = {
		'StudentID' : Item[0],
		#'UserName' : Item[1],
		'IP' : Item[2]
	}
	
	# Intialize location with "None"
	Location = None
	
	# Lookup IP if requested
	if Locate:
		for FromCache in [True, False]:
			for Depth in [1,2,3,4]:
				# Try to locate IP in database with given depth
				Location = IPLookup(JSONClean['IP'], Depth, FromCache)
				# Exit loop if valid location found
				if Location:
					break
			if Location:
				break
			
	# Add location JSON field to output JSON item
	JSONClean.update({'Location' : Location})
			
	# Return clean JSON item
	return JSONClean

# IP Lookup
def IPLookup(IP, Depth, FromCache):
	
	# Check if IP database exists
	if not os.path.isfile(IPTablePath):
		cprint('[EdX Log] [StudentIP Data] [Error] IPLookup() - IP database file not found: %s' % IPTablePath, 'red')
		exit()
	
		
	IPArray = re.findall(r'(\d*).(\d*).(\d*).(\d*)', IP)[0]
	
	# Create IP cache file if it doesn't exist
	if not os.path.isfile('.ipcache'):
		open('.ipcache', 'a').close()
		
	# Create IP-range cache file if it doesn't exist
	if not os.path.isfile('.iprangecache'):
		open('.iprangecache', 'a').close()
	
	#----------------------------
	# Look up IP in IP Cache File
	#----------------------------
	StartTime = time.time()
	
	pipe = subprocess.Popen(['grep', IP+' : ', '.ipcache'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
	stdout, stderr = pipe.communicate()
	
	if len(stdout)>1:

		LocationItem = re.findall(r'\s\:\s([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)', stdout)[0]
		
		LocationJSON = {
			'LocalIPRange' : {
				'Start' : LocationItem[0],
				'End'	: LocationItem[1]
			},
			'Country' : {
				'Code' : LocationItem[2],
				'Name' : GetCountryName(LocationItem[2])
			},
			'District' : LocationItem[3],
			'City' : LocationItem[4],
			'Coordinates' : {
				'Latitude' : LocationItem[5],
				'Longitude' : LocationItem[6]
			},
			'TimeZone' : {
				'Offset' : LocationItem[7],
				'Name' : LocationItem[8].replace('\n','')
			}
		}
		return LocationJSON
	
	else:
		
		StartTime = time.time()
		if FromCache:
			if Depth==1:
				Command = ['grep', '[^0-9]%s\.%s\.%s\.[0-9]*' % (IPArray[0], IPArray[1], IPArray[2]), '.iprangecache']
			elif Depth==2:
				Command = ['grep', '[^0-9]%s\.%s\.[0-9]*\.[0-9]*' % (IPArray[0], IPArray[1]), '.iprangecache']
			elif Depth==3:
				Command = ['grep', '[^0-9]%s\.[0-9]*\.[0-9]*\.[0-9]*' % (IPArray[0]), '.iprangecache']
			else:
				Command = ['grep', '[^0-9][0-9]*\.[0-9]*\.[0-9]*\.[0-9]*', '.iprangecache']
		else:
			if Depth==1:
				Command = ['grep', '[^0-9]%s\.%s\.%s\.[0-9]*' % (IPArray[0], IPArray[1], IPArray[2]), IPTablePath]
			elif Depth==2:
				Command = ['grep', '[^0-9]%s\.%s\.[0-9]*\.[0-9]*' % (IPArray[0], IPArray[1]), IPTablePath]
				#print Command
			elif Depth==3:
				Command = ['grep', '[^0-9]%s\.[0-9]*\.[0-9]*\.[0-9]*' % (IPArray[0]), IPTablePath]
			else:
				Command = ['grep', '[^0-9][0-9]*\.[0-9]*\.[0-9]*\.[0-9]*', IPTablePath]
		
		
		pipe = subprocess.Popen(Command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
		stdout, stderr = pipe.communicate()
		
		if len(stdout)>1:
			
			Output = stdout.splitlines()
			
			IPRangeListForCache = []
			
			for Match in Output:
				
				LocationItem_Match = re.findall(r'([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)\,([^\,]*)', Match)
				
				if len(LocationItem_Match)>0:
					LocationItem = LocationItem_Match[0]
				else:
					cprint('[EdX Log] [StudentIP Data] [Error] IPLookup() - Format error on IP database: %s' % Match, 'red')
					exit()
					
				if not FromCache:
					IPRangeListForCache.append(Match)
					
				if IPv4Address(unicode(IP)) >= IPv4Address(unicode(LocationItem[0])) and IPv4Address(unicode(IP)) <= IPv4Address(unicode(LocationItem[1])):
					LocationJSON = {
						'LocalIPRange' : {
							'Start' : LocationItem[0],
							'End'	: LocationItem[1]
						},
						'Country' : {
							'Code' : LocationItem[2],
							'Name' : GetCountryName(LocationItem[2])
						},
						'District' : LocationItem[3],
						'City' : LocationItem[4],
						'Coordinates' : {
							'Latitude' : LocationItem[5],
							'Longitude' : LocationItem[6]
						},
						'TimeZone' : {
							'Offset' : LocationItem[7],
							'Name' : LocationItem[8].replace('\n','')
						}
					}

					f = open('.ipcache', 'a')
					Line = IP+' : '+','.join(LocationItem)
					f.write(Line+'\n')
					f.close()
					
					#print Match
					f = open('.iprangecache', 'a')
					f.write(Match+'\n')
					f.close()
					
					return LocationJSON
			
			#f = open('.iprangecache', 'a')
			#for IPRangeItem in IPRangeListForCache:
			#	f.write(IPRangeItem+'\n')
			#f.close()
					
		else:
		
			return None
			
	return None
	
	
# Get country name from country code
def GetCountryName(CountryCode):
	if CountryCode=='YU':
		return 'Yugoslavia'
	elif CountryCode=='CS':
		return 'Serbia and Montenegro'
	else:
		CountryName = pycountry.countries.get(alpha2=str(CountryCode)).name
		return unicodedata.normalize('NFKD', CountryName).encode('ascii','ignore')
	

#=========================================================
# STUDENT PERSONAL INFO PARSING FUNCTIONS
#=========================================================




#=========================================================
# VIDEO PARSING FUNCTIONS
#=========================================================

# Parse FILE with video metadata
def ParseVideoFile(FilePath, KeepAlive=False):
	
	# Open and parse XML file
	f = open(FilePath, 'r')
	XMLRoot = etree.fromstring('<root>%s</root>' % f.read())
	f.close()
	
	# Get video ID
	try:
		Match = re.findall(r'(\d{4}\-\d{2}\-\d{2})[^/]*/([^/]*)/video/([a-zA-Z0-9]*).xml$', FilePath)[0]
		LastLoggedDate = Match[0]
		CourseID = Match[1]
		VideoID = Match[2]
	except:
		cprint('[EdX Log] [Video Data] [Error] ParseVideoFile() - Could not parse Video ID from file path.\nIn order to parse, the file path must contain the following pattern: *YYYY-MM-DD*/COURSEID/video/VIDEOID.xml, where YYYY-MM-DD is the EdX log date, COURSEID is a string not containing a forward slash, and VIDEOID is an alphanumeric string of length 32.', 'red')
		exit()
		
	# Get list of all video elemnets
	XMLObjList = XMLRoot.xpath('//video')
	
	# Parse list of video elements
	VideoMetadataList = ParseVideoList(XMLObjList, CourseID, VideoID, LastLoggedDate, KeepAlive)
	
	# Return video metadata JSON list
	return VideoMetadataList
	
	
# Parse LIST with video metadata
def ParseVideoList(XMLObjList, CourseID, VideoID, LastLoggedDate, KeepAlive=False):
	
	# Loop through list of XML objects
	VideoMetadataList = []
	for XMLVideoRoot in XMLObjList:
		# Get JSON item from XML video element
		VideoMetadata = ParseVideoItem(XMLVideoRoot, KeepAlive)
		#printjson(VideoMetadata)

		# Add to video metadata JSON list
		if VideoMetadata:
			VideoMetadata.update({'CourseID' : CourseID, 'VideoID' : VideoID, 'LastLoggedDate' : LastLoggedDate})
			#printjson(VideoMetadata)
			VideoMetadataList.append(VideoMetadata)
			#time.sleep(float(randrange(5))/100.0)
			
	# Return video metadata JSON list
	return VideoMetadataList

# Parse ITEM with video metadata
def ParseVideoItem(XMLVideoRoot, KeepAlive=False):
	
	# Get basic data
	URLName = XMLVideoRoot.get('url_name')
	Title = XMLVideoRoot.get('display_name')
	Downloadable = XMLVideoRoot.get('download_video')
	HTML5Sources = XMLVideoRoot.get('html5_sources')
	SourceURL = XMLVideoRoot.get('source')
	Subtitles = XMLVideoRoot.get('sub')
	YoutubeID = XMLVideoRoot.get('youtube_id_1_0')
	YoutubeTAG = XMLVideoRoot.get('youtube')
	
	# Return if Youtube ID not found in XML
	if not YoutubeID:
		return False
	
	# Determine video length
	URL = 'www.youtube.com/watch?v=%s' % YoutubeID
	Length = GetYoutubeVideoLength(YoutubeID, KeepAlive)
	
	# Build video metadata dict
	VideoMetadata = {'DepthInHierarchy' : 0, 'Title' : Title, 'Length' : Length, 'Downloadable' : Downloadable, 'HTML5Sources' : HTML5Sources, 'SourceURL' : SourceURL, 'Subtitles' : Subtitles, 'YoutubeID' : YoutubeID, 'YoutubeTAG' : YoutubeTAG, 'URLName' : URLName}
	
	# Return video metadata dict
	return VideoMetadata

# Get video length of a Youtube-hosted video
def GetYoutubeVideoLength(YoutubeID, KeepAlive):
	
	# Build HTTP request
	site= 'https://gdata.youtube.com/feeds/api/videos/%s?v=2' % YoutubeID
	hdr = {'User-Agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.11 (KHTML, like Gecko) Chrome/23.0.1271.64 Safari/537.11',
	       'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
	       'Accept-Charset': 'ISO-8859-1,utf-8;q=0.7,*;q=0.3',
	       'Accept-Encoding': 'none',
	       'Accept-Language': 'en-US,en;q=0.8',
	       'Connection': 'keep-alive'}
	
	# Powers of 2 exponent (for sleep function)
	n = 1
	
	# Enter "keep alive" loop
	while True:
	
		# Execute HTTP request
		req = urllib2.Request(site, headers=hdr)
		
		# Try to parse HTTP response
		try:
		    page = urllib2.urlopen(req)
		    s = page.read()
		    break
		    
		# Return if failed or stay alive
		except urllib2.HTTPError, e:
			ErrorMsg = e.fp.read()
			if 'ResourceNotFoundException' in ErrorMsg:
				cprint('[EdX Log] [Video Data] [Warning] Video not found on Youtube server. Assigned "null" length to JSON item.', 'magenta')
				return None
			if 'quota' in ErrorMsg:
				cprint('[EdX Log] [Video Data] [Error] GetYoutubeVideoLength() - Blocked by Youtube due to excessive requests. Use "KeepAlive=True" to keep trying.\nYoutube error message: %s' % ErrorMsg, 'red')
				
				# Retry if KeepAlive flag is ON
				if KeepAlive:
					PowerOfTwo = math.pow(2, n)
					if PowerOfTwo<=256:
						cprint('KeepAlive is ON. Waiting %s seconds before retry...' % str(PowerOfTwo), 'red')
						time.sleep(PowerOfTwo)
						n += 1
						continue
					else:
						cprint('Access blocked by Youtube. Giving up...' % str(PowerOfTwo), 'red')
				# Fail if KeepAlive flag is OFF
				else:
					exit()
			cprint('[EdX Log] [Video Data] [Error] GetYoutubeVideoLength() - Failed to determine video length.\nYoutube error message: %s' % ErrorMsg, 'red')
			exit()
	
	# Parse video length out of Youtube HTTP response
	d = parseString(s)
	e = d.getElementsByTagName('yt:duration')[0]
	a = e.attributes['seconds']
	v = int(a.value)
	Length = str(timedelta(seconds=v))
	
	# Return video length in hh:mm:ss format
	return Length
	

#=========================================================
# PROBLEM PARSING FUNCTIONS
#=========================================================


# Parse FILE with Problem metadata
def ParseProblemFile(FilePath):
	
	# Open and parse XML file
	f = open(FilePath, 'r')
	XMLRoot = etree.fromstring('<root>%s</root>' % f.read().decode('latin-1'))
	f.close()
	
	# Get Problem ID
	try:
		Match = re.findall(r'(\d{4}\-\d{2}\-\d{2})[^/]*/([^/]*)/problem/([a-zA-Z0-9]*).xml$', FilePath)[0]
		LastLoggedDate = Match[0]
		CourseID = Match[1]
		ProblemID = Match[2]
	except:
		cprint('[EdX Log] [Problem Data] [Error] ParseProblemFile() - Could not parse Problem ID from file path.\nIn order to parse, the file path must contain the following pattern: *YYYY-MM-DD*/COURSEID/problem/PROBLEMID.xml, where YYYY-MM-DD is the EdX log date, COURSEID is a string not containing a forward slash, and PROBLEMID is an alphanumeric string of length 32.', 'red')
		exit()
		
	# Get list of all Problem elemnets
	XMLObjList = XMLRoot.xpath('//problem')
	
	# Parse list of Problem elements
	ProblemMetadataList = ParseProblemList(XMLObjList, CourseID, ProblemID, LastLoggedDate)
	
	# Return Problem metadata JSON list
	return ProblemMetadataList

	
# Parse LIST with Problem metadata
def ParseProblemList(XMLObjList, CourseID, ProblemID, LastLoggedDate):
	
	# Loop through list of XML objects
	ProblemMetadataList = []
	for XMLProblemRoot in XMLObjList:
	
		# Get JSON item from XML Problem element
		ProblemMetadata = ParseProblemItem(XMLProblemRoot, ProblemID)

		# Add to Problem metadata JSON list
		if ProblemMetadata:
			ProblemMetadata.update({'CourseID' : CourseID, 'ProblemID' : ProblemID, 'LastLoggedDate' : LastLoggedDate})
			ProblemMetadataList.append(ProblemMetadata)
			
	# Return Problem metadata JSON list
	return ProblemMetadataList

# Parse ITEM with Problem metadata
def ParseProblemItem(XMLProblemRoot, ProblemID):
	
	# Get basic problem attributes
	DisplayName = XMLProblemRoot.get('display_name')
	MaxAttempts = XMLProblemRoot.get('max_attempts')
	
	# Get full text content in XML
	FullContent = ''
	for element in list(XMLProblemRoot.iter()):
		if element.text:
			FullContent += element.text.encode('utf8')
	
	# Initialize list of problem parts' metadata
	ProblemPartMetadataList = []
	
	# Search for know types of problem modules
	for Type in ['choiceresponse', 'multiplechoiceresponse', 'solution', 'script', 'customresponse', 'numericalresponse', 'coderesponse', 'drag_and_drop_input', 'formularesponse', 'imageresponse', 'optioninput', 'optionresponse', 'stringresponse', 'symbolicresponse']:
	
		# For detected problem module, get list of instances through XML Xpath
		for Obj in XMLProblemRoot.xpath('//'+Type):
			
			# Convert module XML element into XML string
			XMLStr = ElementTree.tostring(Obj, method='xml')
			
			# Remove parsing errors
			XMLStr = re.findall(r'<.*>', XMLStr, re.DOTALL)[0]
			
			# Convert XML tree structure into JSON-type python dict
			ProblemTree = xmltodict.parse(XMLStr)
			
			# Build problem part metadata dict
			ProblemPartMetadata = {'ProblemPartID' : None, 'ParentProblemID' : ProblemID, 'PartType' : Type, 'PartTree' : ProblemTree}
			
			# Add to list of problem parts
			ProblemPartMetadataList.append(ProblemPartMetadata)
			
		# END FOR ----------
		
	# END FOR ----------
	
	# Build problem metadata dict
	ProblemMetadata = {'ProblemID' : ProblemID, 'ProblemParts' : ProblemPartMetadataList, 'FullContent' : FullContent, 'MaxAttempts' : MaxAttempts, 'DisplayName' : DisplayName}
	
	# Return problem metadata dict
	return ProblemMetadata

# END DEF ParseProblemItem ----------

#=========================================================
# MONGO-DB MANAGEMENT FUNCTIONS
#=========================================================

def MongoDB_writefilelist(Collection, JSONFileList, ItemClass):
	
	LogLines = []
	
	for JSONFilePath in JSONFileList:
		LogLines += MongoDB_writefile(Collection, JSONFilePath, ItemClass)
		
	return LogLines
	

def MongoDB_writefile(Collection, JSONFilePath, ItemClass):

	JSONItemList = LoadEventFile(JSONFilePath)
	
	LogLines = []
	ShellMSG = '%s [MongoDB] [%s Data] Loaded JSON file: %s' % (ISO8601_utcnow(), ItemClass, JSONFilePath)
	print ShellMSG
	LogLines.append(ShellMSG)
			
	LogLines += MongoDB_writelist(Collection, JSONItemList, ItemClass)
	
	ShellMSG = '%s [MongoDB] [%s Data] [Success] Done processing JSON file: %s' % (ISO8601_utcnow(), ItemClass, JSONFilePath)
	print ShellMSG
	LogLines.append(ShellMSG)
	
	return LogLines


def MongoDB_writelist(Collection, JSONItemList, ItemClass):

	LogLines = []
	for JSONItem in JSONItemList:	
		ShellMSG = MongoDB_write(Collection, JSONItem, ItemClass)
		if False:#ShellMSG[0]:
			cprint(ShellMSG[0], ShellMSG[1])
			if ShellMSG[1]=='red':
				exit()
			else:
				LogLines.append(ShellMSG[0])
		
	return LogLines
	
	

def MongoDB_open():
	
	# Connection to Mongo DB
	try:
		MongoID = pymongo.MongoClient()
		print "Connected to MongoDB"
	except pymongo.errors.ConnectionFailure, e:
		print "Failed to connect: %s" % e 
	
	# Get database pointer
	return MongoID
	
def MongoDB_read():
	return
	
def MongoDB_write(Collection, JSONItem, ItemClass):
	
	# Create document from JSON Item
	Document = json.loads(JSONItem)
	

	#----------------------------
	# Click or SignUp Event Item
	#----------------------------
	if ItemClass=='Click' or ItemClass=='SignUp':
	
		Document.update({'_id' : Document['Event']['EventID']})
		
	#-----------------------------
	# Forum Event + Metadata Item
	#-----------------------------
	if ItemClass=='Forum':
	
		if Document['Event']['EventType']=='Forum.Thread.Launch':
			Document.update({'_id' : Document['Event']['EventMetadata']['ThreadMetadata']['ThreadID']})
		elif Document['Event']['EventType']=='Forum.Thread.PostOn':
			Document.update({'_id' : Document['Event']['EventMetadata']['PostMetadata']['PostID']})
		elif Document['Event']['EventType']=='Forum.Post.CommentOn':
			Document.update({'_id' : Document['Event']['EventMetadata']['CommentMetadata']['CommentID']})
		else:
			e = 'Unknown forum event type.'
			ShellMSG = '%s [MongoDB] [%s Data] [Error] MongoDB_write() - Unable to add item: {\'_id\' : \'%s\'}. Error message: %s' % (ISO8601_utcnow(), ItemClass, Document['_id'], e)
			return [ShellMSG, 'red']
	
	
	if ItemClass=='StudentIP':
	
		Document.update({'_id' : Document['StudentID']})
		
	if ItemClass=='Video':
	
		Document.update({'_id' : Document['VideoID']})
	
	if ItemClass=='Problem':
	
		Document.update({'_id' : Document['ProblemID']})
	
	#------------------------------------------------
	# Add or Replace JSON Item as New Mongo Document
	#------------------------------------------------
	try:
		Collection.save(Document) # save = replace
#		if Collection.find_one({'_id' : Document['_id']}):
			#Collection.save(Document)
		#ShellMSG = '%s [MongoDB] [%s Data] [Item added] {\'_id\' : \'%s\'}' % (ISO8601_utcnow(), ItemClass, Document['_id'])
		#cprint(ShellMSG, 'green')
		#return [ShellMSG, 'cyan']
#			ShellMSG = '%s [MongoDB] [%s Data] [Warning] Item already exists: {\'_id\' : \'%s\'}' % (ISO8601_utcnow(), ItemClass, Document['_id'])
#			return [ShellMSG, 'magenta']
#		else:
#			Collection.insert(Document)
#			ShellMSG = '%s [MongoDB] [%s Data] [Success] Item added: {\'_id\' : \'%s\'}' % (ISO8601_utcnow(), ItemClass, Document['_id'])
#			return [ShellMSG, 'green']
		return True
	except pymongo.errors.DuplicateKeyError, e:
	
		ShellMSG = '%s [MongoDB] [%s Data] [Error] MongoDB_write() - Unable to add item: {\'_id\' : \'%s\'}. Error message: %s' % (ISO8601_utcnow(), ItemClass, Document['_id'], e)
		cprint(ShellMSG, 'red')
		return False#[ShellMSG, 'red']

