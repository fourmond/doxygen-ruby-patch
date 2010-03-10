/******************************************************************************
 *
 *
 *
 * Copyright (C) 1997-2010 by Dimitri van Heesch.
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation under the terms of the GNU General Public License is hereby
 * granted. No representations are made about the suitability of this software
 * for any purpose. It is provided "as is" without express or implied warranty.
 * See the GNU General Public License for more details.
 *
 * Documents produced by Doxygen are derivative works derived from the
 * input used in their production; they are not affected by this license.
 *
 * ----------------------------------------------------------------------------
 *
 * Slovak translation by Stanislav Kudlac (skudlac@pobox.sk)
 *
 * ----------------------------------------------------------------------------
 */

#ifndef TRANSLATOR_SK_H
#define TRANSLATOR_SK_H

class TranslatorSlovak : public TranslatorAdapter_1_2_18
{
  private:
	/*! The Decode() inline assumes the source written in the
		Windows encoding (maintainer only dependent).
	 */
	inline QCString Decode(const QCString & sInput)
	{
//#ifdef _WIN32
	  return sInput;
//#else
//	  return Win1250ToISO88592(sInput);
//#endif
	}

  public:
	// --- Language control methods -------------------

	virtual QCString idLanguage()
	{ return "slovak"; }

	virtual QCString latexLanguageSupportCommand()
	{ return "\\usepackage[slovak]{babel}\n"; }

	/*! return the language charset. This will be used for the HTML output */
	virtual QCString idLanguageCharset()
	{
//#ifdef _WIN32
		return "windows-1250";
//#else
//		return "iso-8859-2";
//#endif
	}

	// --- Language translation methods -------------------

	/*! used in the compound documentation before a list of related functions. */
	virtual QCString trRelatedFunctions()
	{ return Decode("S�visiace funkcie"); }

	/*! subscript for the related functions. */
	virtual QCString trRelatedSubscript()
	{ return Decode("(Uveden� funkcie nies� �lensk�mi funkciami.)"); }

	/*! header that is put before the detailed description of files, classes and namespaces. */
	virtual QCString trDetailedDescription()
	{ return Decode("Detailn� popis"); }

	/*! header that is put before the list of typedefs. */
	virtual QCString trMemberTypedefDocumentation()
	{ return Decode("Dokument�cia k �lensk�m typom"); }

	/*! header that is put before the list of enumerations. */
	virtual QCString trMemberEnumerationDocumentation()
	{ return Decode("Dokument�cia k �lensk�m enumer�ci�m"); }

	/*! header that is put before the list of member functions. */
	virtual QCString trMemberFunctionDocumentation()
	{ return Decode("Dokument�cia k met�dam"); }

	/*! header that is put before the list of member attributes. */
	virtual QCString trMemberDataDocumentation()
	{
	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		return Decode("Dokument�cia k polo�k�m");
	  }
	  else
	  {
		return Decode("Dokument�cia k d�tov�m �lenom");
	  }
	}

	/*! this is the text of a link put after brief descriptions. */
	virtual QCString trMore()
	{ return Decode("..."); }

	/*! put in the class documentation */
	virtual QCString trListOfAllMembers()
	{ return Decode("Zoznam v�etk�ch �lenov."); }

	/*! used as the title of the "list of all members" page of a class */
	virtual QCString trMemberList()
	{ return Decode("Zoznam �lenov triedy"); }

	/*! this is the first part of a sentence that is followed by a class name */
	virtual QCString trThisIsTheListOfAllMembers()
	{ return Decode("Tu n�jdete �pln� zoznam �lenov triedy "); }

	/*! this is the remainder of the sentence after the class name */
	virtual QCString trIncludingInheritedMembers()
	{ return Decode(", vr�tane v�etk�ch zdeden�ch �lenov."); }

	/*! this is put at the author sections at the bottom of man pages.
	 *	parameter s is name of the project name.
	 */
	virtual QCString trGeneratedAutomatically(const char *s)
	{ QCString result="Generovan� automaticky programom Doxygen "
					  "zo zdrojov�ch textov";
	  if (s) result+=(QCString)" projektu "+s;
	  result+=".";
	  return Decode(result);
	}

	/*! put after an enum name in the list of all members */
	virtual QCString trEnumName()
	{ return Decode("meno enumer�cie"); }

	/*! put after an enum value in the list of all members */
	virtual QCString trEnumValue()
	{ return Decode("hodnota enumer�cie"); }

	/*! put after an undocumented member in the list of all members */
	virtual QCString trDefinedIn()
	{ return Decode("definovan� v"); }

	// quick reference sections

	/*! This is put above each page as a link to the list of all groups of
	 *	compounds or files (see the \\group command).
	 */
	virtual QCString trModules()
	{ return Decode("Moduly"); }

	/*! This is put above each page as a link to the class hierarchy */
	virtual QCString trClassHierarchy()
	{ return Decode("Hierarchia tried"); }

	/*! This is put above each page as a link to the list of annotated classes */
	virtual QCString trCompoundList()
	{
	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		return Decode("D�tov� �trukt�ry");
	  }
	  else
	  {
		return Decode("Zoznam tried");
	  }
	}

	/*! This is put above each page as a link to the list of documented files */
	virtual QCString trFileList()
	{ return Decode("Zoznam s�borov"); }

	/*! This is put above each page as a link to the list of all verbatim headers */
	virtual QCString trHeaderFiles()
	{ return Decode("Zoznam hlavi�kov�ch s�borov"); }

	/*! This is put above each page as a link to all members of compounds. */
	virtual QCString trCompoundMembers()
	{
	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		return Decode("D�tov� polo�ky");
	  }
	  else
	  {
		return Decode("Zoznam �lenov tried");
	  }
	}

	/*! This is put above each page as a link to all members of files. */
	virtual QCString trFileMembers()
	{
	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		return Decode("Glob�lne symboly");
	  }
	  else
	  {
		return Decode("Symboly v s�boroch");
	  }
	}

	/*! This is put above each page as a link to all related pages. */
	virtual QCString trRelatedPages()
	{ return Decode("Ostatn� str�nky"); }

	/*! This is put above each page as a link to all examples. */
	virtual QCString trExamples()
	{ return Decode("Pr�klady"); }

	/*! This is put above each page as a link to the search engine. */
	virtual QCString trSearch()
	{ return Decode("H�ada�"); }

	/*! This is an introduction to the class hierarchy. */
	virtual QCString trClassHierarchyDescription()
	{ return Decode("Tu n�jdete zoznam, vyjadruj�ci vz�ah dedi�nosti tried. "
			 "Je zoraden� pribli�ne (ale nie �plne) pod�a abecedy:");
	}

	/*! This is an introduction to the list with all files. */
	virtual QCString trFileListDescription(bool extractAll)
	{
	  QCString result="Tu n�jdete zoznam v�etk�ch ";
	  if (!extractAll) result+="dokumentovan�ch ";
	  result+="s�borov so stru�n�mi popismi:";
	  return Decode(result);
	}

	/*! This is an introduction to the annotated compound list. */
	virtual QCString trCompoundListDescription()
	{
	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		return Decode("Nasleduj�ci zoznam obsahuje identifik�ciu d�tov�ch "
					  "�trukt�r a ich stru�n� popisy:");
	  }
	  else
	  {
		return Decode("Nasleduj�ci zoznam obsahuje predov�etk�m identifik�ciu "
					  "tried, ale nach�dzaj� sa tu i �al�ie netrivi�lne prvky, "
					  "ako s� �trukt�ry (struct), uniony (union) a rozhrania "
					  "(interface). V zozname s� uveden� ich stru�n� "
					  "popisy:");
	  }
	}

	/*! This is an introduction to the page with all class members. */
	virtual QCString trCompoundMembersDescription(bool extractAll)
	{
	  QCString result= "Tu n�jdete zoznam v�etk�ch ";
	  if (!extractAll)
	  {
		result += "dokumentovan�ch ";
	  }

	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		result += "polo�iek �trukt�r (struct) a unionov (union) ";
	  }
	  else
	  {
		result += "�lenov tried ";
	  }

	  result += "s odkazmi na ";

	  if (!extractAll)
	  {
		if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
		{
		  result += "dokument�ciu �trukt�r/unionov, ku ktor�m prisl�chaj�:";
		}
		else
		{
		  result += "dokument�ciu tried, ku ktor�m prisl�chaj�:";
		}
	  }
	  else
	  {
		if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
		{
		  result+="�trukt�ry/uniony, ku ktor�m prisl�chaj�:";
		}
		else
		{
		  result+="triedy, ku ktor�m prisl�chaj�:";
		}
	  }

	  return Decode(result);
	}

	/*! This is an introduction to the page with all file members. */
	virtual QCString trFileMembersDescription(bool extractAll)
	{
	  QCString result="Tu n�jdete zoznam v�etk�ch ";
	  if (!extractAll) result+="dokumentovan�ch ";

	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		result+="funkci�, premenn�ch, makier, enumer�ci� a defin�ci� typov (typedef) "
				"s odkazmi na ";
	  }
	  else
	  {
		result+="symbolov, ktor� s� definovan� na �rovni svojich s�borov. "
				"Pre ka�d� symbol je uveden� odkaz na ";
	  }

	  if (extractAll)
		result+="s�bory, ku ktor�m prisl�chaj�:";
	  else
		result+="dokument�ciu:";

	  return Decode(result);
	}

	/*! This is an introduction to the page with the list of all header files. */
	virtual QCString trHeaderFilesDescription()
	{ return Decode("Tu n�jdete hlavi�kov� s�bory, ktor� tvoria "
			 "aplika�n� programov� rozhranie (API):"); }

	/*! This is an introduction to the page with the list of all examples */
	virtual QCString trExamplesDescription()
	{ return Decode("Tu n�jdete zoznam v�etk�ch pr�kladov:"); }

	/*! This is an introduction to the page with the list of related pages */
	virtual QCString trRelatedPagesDescription()
	{ return Decode("Nasleduj�ci zoznam odkazuje na �al�ie str�nky projektu, "
					"ktor� maj� charakter usporiadan�ch zoznamov inform�ci�, "
					"pozbieran�ch z r�znych miest v zdrojov�ch s�boroch:"); }

	/*! This is an introduction to the page with the list of class/file groups */
	virtual QCString trModulesDescription()
	{ return Decode("Tu n�jdete zoznam v�etk�ch modulov:"); }

	/*! This sentences is used in the annotated class/file lists if no brief
	 * description is given.
	 */
	virtual QCString trNoDescriptionAvailable()
	{ return Decode("Popis nieje k dispoz�cii"); }

	// index titles (the project name is prepended for these)


	/*! This is used in HTML as the title of index.html. */
	virtual QCString trDocumentation()
	{ return Decode("Dokument�cia"); }

	/*! This is used in LaTeX as the title of the chapter with the
	 * index of all groups.
	 */
	virtual QCString trModuleIndex()
	{ return Decode("Register modulov"); }

	/*! This is used in LaTeX as the title of the chapter with the
	 * class hierarchy.
	 */
	virtual QCString trHierarchicalIndex()
	{ return Decode("Register hierarchie tried"); }

	/*! This is used in LaTeX as the title of the chapter with the
	 * annotated compound index.
	 */
	virtual QCString trCompoundIndex()
	{
	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		return Decode("Register d�tov�ch �trukt�r");
	  }
	  else
	  {
		return Decode("Register tried");
	  }
	}

	/*! This is used in LaTeX as the title of the chapter with the
	 * list of all files.
	 */
	virtual QCString trFileIndex()
	{ return Decode("Register s�borov"); }

	/*! This is used in LaTeX as the title of the chapter containing
	 *	the documentation of all groups.
	 */
	virtual QCString trModuleDocumentation()
	{ return Decode("Dokument�cia modulov"); }

	/*! This is used in LaTeX as the title of the chapter containing
	 *	the documentation of all classes, structs and unions.
	 */
	virtual QCString trClassDocumentation()
	{ return Decode("Dokument�cia tried"); }

	/*! This is used in LaTeX as the title of the chapter containing
	 *	the documentation of all files.
	 */
	virtual QCString trFileDocumentation()
	{ return Decode("Dokument�cia s�borov"); }

	/*! This is used in LaTeX as the title of the chapter containing
	 *	the documentation of all examples.
	 */
	virtual QCString trExampleDocumentation()
	{ return Decode("Dokument�cia pr�kladov"); }

	/*! This is used in LaTeX as the title of the chapter containing
	 *	the documentation of all related pages.
	 */
	virtual QCString trPageDocumentation()
	{ return Decode("Dokument�cia s�visiacich str�nok"); }

	/*! This is used in LaTeX as the title of the document */
	virtual QCString trReferenceManual()
	{ return Decode("Referen�n� pr�ru�ka"); }

	/*! This is used in the documentation of a file as a header before the
	 *	list of defines
	 */
	virtual QCString trDefines()
	{ return Decode("Defin�cia makier"); }

	/*! This is used in the documentation of a file as a header before the
	 *	list of function prototypes
	 */
	virtual QCString trFuncProtos()
	{ return Decode("Prototypy"); }

	/*! This is used in the documentation of a file as a header before the
	 *	list of typedefs
	 */
	virtual QCString trTypedefs()
	{ return Decode("Defin�cia typov"); }

	/*! This is used in the documentation of a file as a header before the
	 *	list of enumerations
	 */
	virtual QCString trEnumerations()
	{ return Decode("Enumer�cie"); }

	/*! This is used in the documentation of a file as a header before the
	 *	list of (global) functions
	 */
	virtual QCString trFunctions()
	{ return Decode("Funkcie"); }

	/*! This is used in the documentation of a file as a header before the
	 *	list of (global) variables
	 */
	virtual QCString trVariables()
	{ return Decode("Premenn�"); }

	/*! This is used in the documentation of a file as a header before the
	 *	list of (global) variables
	 */
	virtual QCString trEnumerationValues()
	{ return Decode("Hodnoty enumer�ci�"); }

	/*! This is used in the documentation of a file before the list of
	 *	documentation blocks for defines
	 */
	virtual QCString trDefineDocumentation()
	{ return Decode("Dokument�cia k defin�ci�m makier"); }

	/*! This is used in the documentation of a file/namespace before the list
	 *	of documentation blocks for function prototypes
	 */
	virtual QCString trFunctionPrototypeDocumentation()
	{ return Decode("Dokument�cia prototypov"); }

	/*! This is used in the documentation of a file/namespace before the list
	 *	of documentation blocks for typedefs
	 */
	virtual QCString trTypedefDocumentation()
	{ return Decode("Dokument�cia defin�ci� typov"); }

	/*! This is used in the documentation of a file/namespace before the list
	 *	of documentation blocks for enumeration types
	 */
	virtual QCString trEnumerationTypeDocumentation()
	{ return Decode("Dokument�cia enumera�n�ch typov"); }

	/*! This is used in the documentation of a file/namespace before the list
	 *	of documentation blocks for enumeration values
	 */
	virtual QCString trEnumerationValueDocumentation()
	{ return Decode("Dokument�cia enumera�n�ch hodn�t"); }

	/*! This is used in the documentation of a file/namespace before the list
	 *	of documentation blocks for functions
	 */
	virtual QCString trFunctionDocumentation()
	{ return Decode("Dokument�cia funkci�"); }

	/*! This is used in the documentation of a file/namespace before the list
	 *	of documentation blocks for variables
	 */
	virtual QCString trVariableDocumentation()
	{ return Decode("Dokument�cia premenn�ch"); }

	/*! This is used in the documentation of a file/namespace/group before
	 *	the list of links to documented compounds
	 */
	virtual QCString trCompounds()
	{
	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		return Decode("D�tov� �trukt�ry");
	  }
	  else
	  {
		return Decode("Triedy");
	  }
	}

	/*! This is used in the standard footer of each page and indicates when
	 *	the page was generated
	 */
	virtual QCString trGeneratedAt(const char *date,const char *projName)
	{
	  QCString result=(QCString)"Generovan� "+date;
	  if (projName) result+=(QCString)" pre projekt "+projName;
	  result+=(QCString)" programom";
	  return Decode(result);
	}

	/*! This is part of the sentence used in the standard footer of each page.
	 */
	virtual QCString trWrittenBy()
	{
	  return Decode(" -- autor ");
	}

	/*! this text is put before a class diagram */
	virtual QCString trClassDiagram(const char *clName)
	{
	  return Decode((QCString)"Diagram dedi�nosti pre triedu "+clName);
	}

	/*! this text is generated when the \\internal command is used. */
	virtual QCString trForInternalUseOnly()
	{ return Decode("Iba pre intern� pou�itie."); }

	/*! this text is generated when the \\reimp command is used. */
	virtual QCString trReimplementedForInternalReasons()
	{ return Decode("Reimplementovan� z intern�ch d�vodov; "
					"aplika�n� rozhranie zachovan�."); }

	/*! this text is generated when the \\warning command is used. */
	virtual QCString trWarning()
	{ return Decode("Pozor"); }

	/*! this text is generated when the \\bug command is used. */
	virtual QCString trBugsAndLimitations()
	{ return Decode("Chyby a obmedzenia"); }

	/*! this text is generated when the \\version command is used. */
	virtual QCString trVersion()
	{ return Decode("Verzia"); }

	/*! this text is generated when the \\date command is used. */
	virtual QCString trDate()
	{ return Decode("D�tum"); }

	/*! this text is generated when the \\return command is used. */
	virtual QCString trReturns()
	{ return Decode("N�vratov� hodnota"); }

	/*! this text is generated when the \\sa command is used. */
	virtual QCString trSeeAlso()
	{ return Decode("Viz tie�"); }

	/*! this text is generated when the \\param command is used. */
	virtual QCString trParameters()
	{ return Decode("Parametre"); }

	/*! this text is generated when the \\exception command is used. */
	virtual QCString trExceptions()
	{ return Decode("V�nimky"); }

	/*! this text is used in the title page of a LaTeX document. */
	virtual QCString trGeneratedBy()
	{ return Decode("Generovan� programom"); }

	// new since 0.49-990307

	/*! used as the title of page containing all the index of all namespaces. */
	virtual QCString trNamespaceList()
	{ return Decode("Zoznam priestorov mien"); }

	/*! used as an introduction to the namespace list */
	virtual QCString trNamespaceListDescription(bool extractAll)
	{
	  QCString result="Tu n�jdete zoznam v�etk�ch ";
	  if (!extractAll) result+="dokumentovan�ch ";
	  result+="priestorov mien so stru�n�m popisom:";
	  return Decode(result);
	}

	/*! used in the class documentation as a header before the list of all
	 *	friends of a class
	 */
	virtual QCString trFriends()
	{ return Decode("Priatelia (friends)"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990405
//////////////////////////////////////////////////////////////////////////

	/*! used in the class documentation as a header before the list of all
	 * related classes
	 */
	virtual QCString trRelatedFunctionDocumentation()
	{ return Decode("Dokument�cia k priate�om (friends)"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990425
//////////////////////////////////////////////////////////////////////////

	/*! used as the title of the HTML page of a class/struct/union */
	virtual QCString trCompoundReference(const char *clName,
									ClassDef::CompoundType compType,
									bool isTemplate)
	{
	  QCString result("Dokument�cia ");
	  if (isTemplate) result+="�abl�ny ";
	  switch(compType)
	  {
		case ClassDef::Class:	   result+="triedy "; break;
		case ClassDef::Struct:	   result+="�trukt�ry "; break;
		case ClassDef::Union:	   result+="unionu "; break;
		case ClassDef::Interface:  result+="rozhrania "; break;
		case ClassDef::Protocol:   result+="protocol "; break; // translate me!
		case ClassDef::Category:   result+="category "; break; // translate me!
		case ClassDef::Exception:  result+="v�nimky "; break;
	  }
	  result+=clName;
	  return Decode(result);
	}

	/*! used as the title of the HTML page of a file */
	virtual QCString trFileReference(const char *fileName)
	{
	  QCString result("Dokument�cia s�boru ");
	  result+=fileName;
	  return Decode(result);
	}

	/*! used as the title of the HTML page of a namespace */
	virtual QCString trNamespaceReference(const char *namespaceName)
	{
	  QCString result("Dokument�cia priestoru mien ");
	  result+=namespaceName;
	  return Decode(result);
	}

	/* these are for the member sections of a class, struct or union */
	virtual QCString trPublicMembers()
	{ return Decode("Verejn� met�dy"); }
	virtual QCString trPublicSlots()
	{ return Decode("Verejn� sloty"); }
	virtual QCString trSignals()
	{ return Decode("Sign�ly"); }
	virtual QCString trStaticPublicMembers()
	{ return Decode("Statick� verejn� met�dy"); }
	virtual QCString trProtectedMembers()
	{ return Decode("Chr�nen� met�dy"); }
	virtual QCString trProtectedSlots()
	{ return Decode("Chr�nen� sloty"); }
	virtual QCString trStaticProtectedMembers()
	{ return Decode("Statick� chr�nen� met�dy"); }
	virtual QCString trPrivateMembers()
	{ return Decode("Priv�tne met�dy"); }
	virtual QCString trPrivateSlots()
	{ return Decode("Priv�tne sloty"); }
	virtual QCString trStaticPrivateMembers()
	{ return Decode("Statick� priv�tne met�dy"); }

	/*! this function is used to produce a comma-separated list of items.
	 *	use generateMarker(i) to indicate where item i should be put.
	 */
	virtual QCString trWriteList(int numEntries)
	{
	  QCString result;
	  int i;
	  // the inherits list contain `numEntries' classes
	  for (i=0;i<numEntries;i++)
	  {
		// use generateMarker to generate placeholders for the class links!
		result+=generateMarker(i); // generate marker for entry i in the list
								   // (order is left to right)

		if (i!=numEntries-1)  // not the last entry, so we need a separator
		{
		  if (i<numEntries-2) // not the fore last entry
			result+=", ";
		  else				  // the fore last entry
			result+=" a ";
		}
	  }
	  return Decode(result);
	}

	/*! used in class documentation to produce a list of base classes,
	 *	if class diagrams are disabled.
	 */
	virtual QCString trInheritsList(int numEntries)
	{
	  QCString result("Ded� od ");
	  result += (numEntries == 1) ? "b�zovej triedy " : "b�zov�ch tried ";
	  result += trWriteList(numEntries)+".";
	  return Decode(result);
	}

	/*! used in class documentation to produce a list of super classes,
	 *	if class diagrams are disabled.
	 */
	virtual QCString trInheritedByList(int numEntries)
	{
	  QCString result("Zdeden� ");
	  result += (numEntries == 1) ? "triedou " : "triedami ";
	  result += trWriteList(numEntries)+".";
	  return Decode(result);
	}

	/*! used in member documentation blocks to produce a list of
	 *	members that are hidden by this one.
	 */
	virtual QCString trReimplementedFromList(int numEntries)
	{
	  QCString result("Reimplementuje ");
	  result += (numEntries == 1) ? "met�du triedy " : "met�dy tried ";
	  result += trWriteList(numEntries)+".";
	  return Decode(result);
	}

	/*! used in member documentation blocks to produce a list of
	 *	all member that overwrite the implementation of this member.
	 */
	virtual QCString trReimplementedInList(int numEntries)
	{
	  QCString result("Reimplementovan� ");
	  result += (numEntries == 1) ? "triedou " : "triedami ";
	  result += trWriteList(numEntries)+".";
	  return Decode(result);
	}

	/*! This is put above each page as a link to all members of namespaces. */
	virtual QCString trNamespaceMembers()
	{ return Decode("Symboly v priestoroch mien"); }

	/*! This is an introduction to the page with all namespace members */
	virtual QCString trNamespaceMemberDescription(bool extractAll)
	{
	  QCString result="Tu n�jdete zoznam v�etk�ch ";
	  if (!extractAll) result+="dokumentovan�ch ";
	  result+="symbolov, ktor� s� definovan� vo svojich priestoroch mien. "
			  "U ka�d�ho je uveden� odkaz na ";
	  if (extractAll)
		result+="dokument�ciu pr�slu�n�ho priestoru mien:";
	  else
		result+="pr�slu�n� priestor mien:";
	  return Decode(result);
	}
	/*! This is used in LaTeX as the title of the chapter with the
	 *	index of all namespaces.
	 */
	virtual QCString trNamespaceIndex()
	{ return Decode("Register priestorov mien"); }

	/*! This is used in LaTeX as the title of the chapter containing
	 *	the documentation of all namespaces.
	 */
	virtual QCString trNamespaceDocumentation()
	{ return Decode("Dokument�cia priestorov mien"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990522
//////////////////////////////////////////////////////////////////////////

	/*! This is used in the documentation before the list of all
	 *	namespaces in a file.
	 */
	virtual QCString trNamespaces()
	{ return Decode("Priestory mien"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990728
//////////////////////////////////////////////////////////////////////////

	/*! This is put at the bottom of a class documentation page and is
	 *	followed by a list of files that were used to generate the page.
	 */
	virtual QCString trGeneratedFromFiles(ClassDef::CompoundType compType,
		bool single)
	{ // here s is one of " Class", " Struct" or " Union"
	  // single is true implies a single file
	  QCString result=(QCString)"Dokument�cia pre ";
	  switch(compType)
	  {
		case ClassDef::Class:	   result+="t�to triedu"; break;
		case ClassDef::Struct:	   result+="t�to �trukt�ru (struct)"; break;
		case ClassDef::Union:	   result+="tento union"; break;
		case ClassDef::Interface:  result+="toto rozhranie"; break;
		case ClassDef::Protocol:   result+="protocol"; break; // translate me!
		case ClassDef::Category:   result+="category"; break; // translate me!
		case ClassDef::Exception:  result+="t�to v�nimku"; break;
	  }
	  result+=" bola generovan� z ";
	  if (single) result+="nasleduj�ceho s�boru:";
	  else		  result+="nasleduj�cich s�borov:";
	  return Decode(result);
	}

	/*! This is in the (quick) index as a link to the alphabetical compound
	 * list.
	 */
	virtual QCString trAlphabeticalList()
	{ return Decode("Register tried"); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-990901
//////////////////////////////////////////////////////////////////////////

	/*! This is used as the heading text for the retval command. */
	virtual QCString trReturnValues()
	{ return Decode("N�vratov� hodnoty"); }

	/*! This is in the (quick) index as a link to the main page (index.html)
	 */
	virtual QCString trMainPage()
	{ return Decode("Hlavn� str�nka"); }

	/*! This is used in references to page that are put in the LaTeX
	 *	documentation. It should be an abbreviation of the word page.
	 */
	virtual QCString trPageAbbreviation()
	{ return Decode("s."); }

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991003
//////////////////////////////////////////////////////////////////////////

	virtual QCString trSources()
	{
	  return Decode("Zdroje");
	}
	virtual QCString trDefinedAtLineInSourceFile()
	{
	  return Decode("Defin�cia je uveden� na riadku @0 v s�bore @1.");
	}
	virtual QCString trDefinedInSourceFile()
	{
	  return Decode("Defin�cia v s�bore @0.");
	}

//////////////////////////////////////////////////////////////////////////
// new since 0.49-991205
//////////////////////////////////////////////////////////////////////////

	virtual QCString trDeprecated()
	{
	  return Decode("Zastaral�");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.0.0
//////////////////////////////////////////////////////////////////////////

	/*! this text is put before a collaboration diagram */
	virtual QCString trCollaborationDiagram(const char *clName)
	{
	  return Decode((QCString)"Diagram tried pre "+clName+":");
	}
	/*! this text is put before an include dependency graph */
	virtual QCString trInclDepGraph(const char *fName)
	{
	  return Decode((QCString)"Graf z�vislost� na vkladan�ch s�boroch "
					"pre "+fName+":");
	}
	/*! header that is put before the list of constructor/destructors. */
	virtual QCString trConstructorDocumentation()
	{
	  return Decode("Dokument�cia kon�truktoru a de�truktoru");
	}
	/*! Used in the file documentation to point to the corresponding sources. */
	virtual QCString trGotoSourceCode()
	{
	  return Decode("Zobrazi� zdrojov� text tohoto s�boru.");
	}
	/*! Used in the file sources to point to the corresponding documentation. */
	virtual QCString trGotoDocumentation()
	{
	  return Decode("Zobrazi� dokument�ciu tohoto s�boru.");
	}
	/*! Text for the \\pre command */
	virtual QCString trPrecondition()
	{
	  return Decode("Prepodmienka");
	}
	/*! Text for the \\post command */
	virtual QCString trPostcondition()
	{
	  return Decode("Postpodmienka");
	}
	/*! Text for the \\invariant command */
	virtual QCString trInvariant()
	{
	  return Decode("Invariant");
	}
	/*! Text shown before a multi-line variable/enum initialization */
	virtual QCString trInitialValue()
	{
	  return Decode("Inicializ�tor:");
	}
	/*! Text used the source code in the file index */
	virtual QCString trCode()
	{
	  return Decode("zdrojov� text");
	}
	virtual QCString trGraphicalHierarchy()
	{
	  return Decode("Grafick� zobrazenie hierarchie tried");
	}
	virtual QCString trGotoGraphicalHierarchy()
	{
	  return Decode("Zobrazi� grafick� podobu hierarchie tried");
	}
	virtual QCString trGotoTextualHierarchy()
	{
	  return Decode("Zobrazi� textov� podobu hierarchie tried");
	}
	virtual QCString trPageIndex()
	{
	  return Decode("Register str�nok");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.1.0
//////////////////////////////////////////////////////////////////////////

	virtual QCString trNote()
	{
	  return Decode("Pozn�mka");
	}
	virtual QCString trPublicTypes()
	{
	  return Decode("Verejn� typy");
	}
	virtual QCString trPublicAttribs()
	{
	  if (Config_getBool("OPTIMIZE_OUTPUT_FOR_C"))
	  {
		return Decode("D�tov� polo�ky");
	  }
	  else
	  {
		return Decode("Verejn� atrib�ty");
	  }
	}
	virtual QCString trStaticPublicAttribs()
	{
	  return Decode("Statick� verejn� atrib�ty");
	}
	virtual QCString trProtectedTypes()
	{
	  return Decode("Chr�nen� typy");
	}
	virtual QCString trProtectedAttribs()
	{
	  return Decode("Chr�nen� atrib�ty");
	}
	virtual QCString trStaticProtectedAttribs()
	{
	  return Decode("Statick� chr�nen� atrib�ty");
	}
	virtual QCString trPrivateTypes()
	{
	  return Decode("Priv�tne typy");
	}
	virtual QCString trPrivateAttribs()
	{
	  return Decode("Priv�tne atrib�ty");
	}
	virtual QCString trStaticPrivateAttribs()
	{
	  return Decode("Statick� priv�tne atrib�ty");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.1.3
//////////////////////////////////////////////////////////////////////////

	/*! Used as a marker that is put before a todo item */
	virtual QCString trTodo()
	{
	  return Decode("Pl�novan� �pravy");
	}
	/*! Used as the header of the todo list */
	virtual QCString trTodoList()
	{
	  return Decode("Zoznam pl�novan�ch �prav");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.1.4
//////////////////////////////////////////////////////////////////////////

	virtual QCString trReferencedBy()
	{
	  return Decode("Pou��va sa v");
	}
	virtual QCString trRemarks()
	{
	  return Decode("Pozn�mky"); // ??? not checked in a context
	}
	virtual QCString trAttention()
	{
	  return Decode("Upozornenie"); // ??? not checked in a context
	}
	virtual QCString trInclByDepGraph()
	{
	  return Decode("Nasleduj�ci graf ukazuje, ktor� s�bory priamo alebo "
			 "nepriamo vkladaj� tento s�bor:");
	}
	virtual QCString trSince()
	{
	  return Decode("Od"); // ??? not checked in a context
	}

////////////////////////////////////////////////////////////////////////////
// new since 1.1.5
//////////////////////////////////////////////////////////////////////////

	/*! title of the graph legend page */
	virtual QCString trLegendTitle()
	{
	  return Decode("Vysvetlivky ku grafu");
	}
	/*! page explaining how the dot graph's should be interpreted */
	virtual QCString trLegendDocs()
	{
	  QCString result(
		"Tu n�jdete vysvetlenie, ako maj� by� interpretovan� grafy, "
		"ktor� boli generovan� programom doxygen.<p>\n"
		"Uva�ujte nasleduj�ci pr�klad:\n"
		"\\code\n"
		"/*! Neviditeln� trieda, ktor� sa v grafe nezobrazuje, preto�e "
		"do�lo k orezaniu grafu. */\n"
		"class Invisible { };\n\n"
		"/*! Trieda, u ktorej do�lo k orezaniu grafu. Vz�ah dedi�nosti "
		"je skryt�. */\n"
		"class Truncated : public Invisible { };\n\n"
		"/* Trieda, ktor� nieje dokumentovan� koment�rmi programu doxygen. */\n"
		"class Undocumented { };\n\n"
		"/*! Odvoden� trieda s verejn�m (public) deden�m b�zovej triedy. */\n"
		"class PublicBase : public Truncated { };\n\n"
		"/*! Odvoden� trieda s chr�nen�m (protected) deden�m b�zovej triedy. */\n"
		"/*! A template class */\n"
		"template<class T> class Templ { };\n\n"
		"class ProtectedBase { };\n\n"
		"/*! Odvoden� trieda s priv�tnym deden�m b�zovej triedy. */\n"
		"class PrivateBase { };\n\n"
		"/*! Trieda, ktor� je vyu��van� triedou Inherited. */\n"
		"class Used { };\n\n"
		"/*! Odvoden� trieda, ktor� r�znym sp�sobom ded� od viacer�ch b�zov�ch "
		"tried. */\n"
		"class Inherited : public PublicBase,\n"
		"                  protected ProtectedBase,\n"
		"                  private PrivateBase,\n"
		"                  public Undocumented,\n"
		"                  public Templ<int>\n"
		"{\n"
		"  private:\n"
		"	 Used *m_usedClass;\n"
		"};\n"
		"\\endcode\n"
		"Pokia� je polo�ka \\c MAX_DOT_GRAPH_HEIGHT konfigura�n�ho s�boru "
		"nastaven� na hodnotu 200, bude vygenerovan� nasleduj�ci graf:"
		"<p><center><img src=\"graph_legend."+Config_getEnum("DOT_IMAGE_FORMAT")+"\"></center>\n"
		"<p>\n"
		"Bloky (tj. uzly) v uvedenom grafe maj� nasleduj�ci v�znam:\n"
		"<ul>\n"
		"<li>�ierne vyplnen� obd�nik reprezentuje �trukt�ru alebo triedu, "
			"pre ktor� bol graf generovan�.\n"
		"<li>Obd�nik s �iernym obrysom ozna�uje dokumentovan� "
			"�trukt�ru alebo triedu.\n"
		"<li>Obd�nik so �ed�m obrysom ozna�uje nedokumentovan� "
			"�trukt�ru alebo triedu.\n"
		"<li>Obd�nik s �erven�m obrysom ozna�uje dokumentovan� "
			"�trukt�ru alebo triedu, pre ktor�\n"
			"nies� zobrazen� v�etky vz�ahy dedi�nosti alebo obsiahnutia. "
			"Graf je orezan� v pr�pade, kedy ho\n"
			"nieje mo�n� umiestni� do vymedzen�ch hran�c.\n"
		"</ul>\n"
		"��pky (tj. hrany grafu) maj� nasleduj�c� v�znam:\n"
		"<ul>\n"
		"<li>Tmavo modr� ��pka sa pou��va pre ozna�enie vz�ahu verejnej "
			"dedi�nosti medzi dvoma triedami.\n"
		"<li>Tmavo zelen� ��pka ozna�uje vz�ah chr�nenej dedi�nosti "
			"(protected).\n"
		"<li>Tmavo �erven� ��pka ozna�uje vz�ah priv�tnej dedi�nosti.\n"
		"<li>Purpurov� ��pka kreslen� �iarkovane sa pou��va v pr�pade, "
			"ak je trieda obsiahnut� v inej triede,\n"
			"alebo ak je pou��van� inou triedou. Je ozna�en� identifik�torom "
			"jednej alebo viacer�ch premenn�ch (objektov), cez ktor�\n"
			"je trieda alebo �trukt�ra zpr�stupnena.\n"
		"</ul>\n");

		return Decode(result);
	}
	/*! text for the link to the legend page */
	virtual QCString trLegend()
	{
	  return Decode("vysvetlivky");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.0
//////////////////////////////////////////////////////////////////////////

	/*! Used as a marker that is put before a test item */
	virtual QCString trTest()
	{
	  return Decode("Test");
	}

	/*! Used as the header of the test list */
	virtual QCString trTestList()
	{
	  return Decode("Zoznam testov");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.1
//////////////////////////////////////////////////////////////////////////

	/*! Used as a section header for KDE-2 IDL methods */
	virtual QCString trDCOPMethods()
	{
	  return Decode("Met�dy DCOP");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.2
//////////////////////////////////////////////////////////////////////////

	/*! Used as a section header for IDL properties */
	virtual QCString trProperties()
	{
	  return Decode("Vlastnosti");
	}
	/*! Used as a section header for IDL property documentation */
	virtual QCString trPropertyDocumentation()
	{
	  return Decode("Dokument�cia k vlastnosti");
	}
//////////////////////////////////////////////////////////////////////////
// new since 1.2.4
//////////////////////////////////////////////////////////////////////////

	/*! Used for Java interfaces in the summary section of Java packages */
	virtual QCString trInterfaces()
	{
	  return Decode("Rozhranie");
	}
	/*! Used for Java classes in the summary section of Java packages */
	virtual QCString trClasses()
	{
	  return Decode("Triedy");
	}
	/*! Used as the title of a Java package */
	virtual QCString trPackage(const char *name)
	{
	  return Decode((QCString)"Bal�k "+name);
	}
	/*! Title of the package index page */
	virtual QCString trPackageList()
	{
	  return Decode("Zoznam bal�kov");
	}
	/*! The description of the package index page */
	virtual QCString trPackageListDescription()
	{
	  return Decode("Tu n�jdete zoznam bal�kov so stru�n�m popisom "
					"(pokia� bol uveden�):");
	}
	/*! The link name in the Quick links header for each page */
	virtual QCString trPackages()
	{
	  return Decode("Bal�ky");
	}
	/*! Used as a chapter title for Latex & RTF output */
	virtual QCString trPackageDocumentation()
	{
	  return Decode("Dokument�cia bal�ku");
	}
	/*! Text shown before a multi-line define */
	virtual QCString trDefineValue()
	{
	  return Decode("Hodnota:");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.5
//////////////////////////////////////////////////////////////////////////

	/*! Used as a marker that is put before a \\bug item */
	virtual QCString trBug()
	{
	  return Decode("Chyba");
	}
	/*! Used as the header of the bug list */
	virtual QCString trBugList()
	{
	  return Decode("Zoznam ch�b");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.6-20010422
//////////////////////////////////////////////////////////////////////////

	/*! Used as ansicpg for RTF file */
	virtual QCString trRTFansicp()
	{
	  return "1250";
	}

	/*! Used as ansicpg for RTF fcharset */
	virtual QCString trRTFCharSet()
	{
	  return "3";
	}

	/*! Used as header RTF general index */
	virtual QCString trRTFGeneralIndex()
	{
	  return "Index";
	}

	/*! This is used for translation of the word that will possibly
	 *	be followed by a single name or by a list of names
	 *	of the category.
	 */
	virtual QCString trClass(bool first_capital, bool singular)
	{
	  QCString result((first_capital ? "Tried" : "tried"));
	  result+=(singular ? "a" : "y");
	  return Decode(result);
	}

	/*! This is used for translation of the word that will possibly
	 *	be followed by a single name or by a list of names
	 *	of the category.
	 */
	virtual QCString trFile(bool first_capital, bool singular)
	{
	  QCString result((first_capital ? "S�bor" : "s�bor"));
	  if (!singular)  result+="y";
	  return Decode(result);
	}

	/*! This is used for translation of the word that will possibly
	 *	be followed by a single name or by a list of names
	 *	of the category.
	 */
	virtual QCString trNamespace(bool first_capital, bool singular)
	{
	  QCString result((first_capital ? "Priestor" : "priestor"));
	  if (!singular)  result+="y";
	  result+=" mien";
	  return Decode(result);
	}

	/*! This is used for translation of the word that will possibly
	 *	be followed by a single name or by a list of names
	 *	of the category.
	 */
	virtual QCString trGroup(bool first_capital, bool singular)
	{
	  QCString result((first_capital ? "Skupin" : "skupin"));
	  result+=(singular ? "a" : "y");
	  return Decode(result);
	}

	/*! This is used for translation of the word that will possibly
	 *	be followed by a single name or by a list of names
	 *	of the category.
	 */
	virtual QCString trPage(bool first_capital, bool singular)
	{
	  QCString result((first_capital ? "Str�nk" : "str�nk"));
	  result+=(singular ? "a" : "y");
	  return Decode(result);
	}

	/*! This is used for translation of the word that will possibly
	 *	be followed by a single name or by a list of names
	 *	of the category.
	 */
	virtual QCString trMember(bool first_capital, bool singular)
	{
	  QCString result((first_capital ? "�len" : "�len"));
	  if (!singular)  result+="y";
	  return Decode(result);
	}

	/*! This is used for translation of the word that will possibly
	 *	be followed by a single name or by a list of names
	 *	of the category.
	 */
	virtual QCString trField(bool first_capital, bool singular)
	{
	  QCString result((first_capital ? "Polo�k" : "polo�k"));
	  result+=(singular ? "a" : "y");
	  return Decode(result);
	}

	/*! This is used for translation of the word that will possibly
	 *	be followed by a single name or by a list of names
	 *	of the category.
	 */
	virtual QCString trGlobal(bool first_capital, bool singular)
	{
	  QCString result((first_capital ? "Glob�ln" : "glob�ln"));
	  result+=(singular ? "y" : "e");
	  return result;
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.7
//////////////////////////////////////////////////////////////////////////

	/*! This text is generated when the \\author command is used and
	 *	for the author section in man pages. */
	virtual QCString trAuthor(bool first_capital, bool singular)
	{
	  QCString result((first_capital ? "Auto" : "auto"));
	  result += (singular) ? "r" : "ri";
	  return result;
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.11
//////////////////////////////////////////////////////////////////////////

	/*! This text is put before the list of members referenced by a member
	 */
	virtual QCString trReferences()
	{
	  return Decode("Odkazuje sa na");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.13
//////////////////////////////////////////////////////////////////////////

	/*! used in member documentation blocks to produce a list of
	 *	members that are implemented by this one.
	 */
	virtual QCString trImplementedFromList(int numEntries)
	{
	  return "Implementuje " + trWriteList(numEntries) + ".";
	}

	/*! used in member documentation blocks to produce a list of
	 *	all members that implement this member.
	 */
	virtual QCString trImplementedInList(int numEntries)
	{
	  return Decode("Implementovan� v " + trWriteList(numEntries) + ".");
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.16
//////////////////////////////////////////////////////////////////////////

	/*! used in RTF documentation as a heading for the Table
	 *	of Contents.
	 */
	virtual QCString trRTFTableOfContents()
	{
	  return "Obsah";
	}

//////////////////////////////////////////////////////////////////////////
// new since 1.2.17
//////////////////////////////////////////////////////////////////////////

	/*! Used as the header of the list of item that have been
	 *	flagged deprecated
	 */
	virtual QCString trDeprecatedList()
	{
	  return "Zastaran� met�dy";
	}
};

#endif // TRANSLATOR_SK_H
