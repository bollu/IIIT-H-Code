class UserController < ApplicationController
  before_action  :kick_out_unauthorized?
    
  # === TAKE SURVEY ===
  def take_survey
    if kick_out_unauthorized? then
      return
    end


    if request.get? then
      @survey = Survey.find_by(survey_params)
      if @survey.nil? then
        flash[:error] = "Unable to find survey " + survey_params[:name]
        redirect_to :controller => 'user', :action => 'mainpage'
      end
    end
    
    if not request.post? then
      return
    end
    # POST Request handling

    @survey = Survey.find_by({id: params[:survey_response][:survey_id]})
    raise "Survey does not exist when answer was submitted" unless not @survey.nil?
    
    # create survey response object and save it
    @survey_response = SurveyResponse.new({
          :survey_id => @survey.id,
          :user_id => @user.id,
      })

    if @survey_response.save then
      flash[:message] =  "Saved Response to survey " + @survey.name
      redirect_to :controller => 'user', :action => 'mainpage'
    else
      flash[:error] = "Survey Response Errored: " + @survey.name
      redirect_to :controller => 'user', :action => 'mainpage'
    end


    # save answers
    params[:answers].each do |qid, ans|
      @q = Question.find_by({id: qid})
      raise "Question does not exist when answer was submitted" unless not @q.nil?

      @a = Answer.new({:survey_response_id => @survey_response.id,
                       :question_id =>  @q.id,
                       :answer => ans})
      # if this fucks up, then you done fucked
      @a.save!
    end

  end

  # === SHOW SURVEY RESULT ===

  def show_survey_result
    if kick_out_unauthorized? then
      return
    end


    if request.get? then
      @survey = Survey.find_by({id: params[:survey][:id]})
      if @survey.nil? then
        flash[:error] = "Unable to find survey " + survey_params[:name]
        redirect_to :controller => 'user', :action => 'mainpage'
        return
      end

      @survey_response = SurveyResponse.find_by({:survey_id => @survey.id })
      puts "===SURVEY RESPONSE==="
      puts @survey_response
      raise "Survey Response for survey |" + @survey.name + "| does not exist" unless not @survey_response.nil?

    end

  end

  # === SIGNUP LOGIN LOGOUT ===
  def signup
    if not request.post? then
        return
    end
    puts "password: " + user_params[:password] + " | confirm: " + user_params[:password_conformation]  
    if user_params[:password_conformation] != user_params[:password] then
        flash[:error]= {:password => [" does not match with conformation password"]}
        redirect_to :controller => 'user', :action => 'signup'
        return
    end

    @user = User.new(user_params)

    if @user.save then
        session["user_id"] = @user.id 
        session["username"] = @user.username 
        redirect_to :controller => 'user', :action => 'mainpage'
    else
        flash[:error] = @user.errors
        redirect_to :controller => 'user', :action => 'signup'
    end
  end

  # use this to kick out unauthorized profiles
  def kick_out_unauthorized?
    @unauthorized_allowed_actions = ['signup', 'login']
    
    if @unauthorized_allowed_actions.include?(params[:action]) then
      return
    end

    # if there is a session ID and the user exists, then allow continue
    if session.has_key?("user_id") and session.has_key?("username") then
      @user = User.find_by("username": session[:username])

      if not @user.nil? and @user.id == session["user_id"] then
        return
      else
        session["user_id"] = nil
      end
    end

    # if not, send back to login 
    redirect_to :controller => 'user', :action => 'login'
  end


  # Use this to automatically redirect to an authorized page
  def auto_redirect_authorized?
    if session.has_key?("user_id") then
      redirect_to_action = "mainpage"
      if params.has_key?(:redirect_to) then
        redirect_to_action = params[:redirect_to]
      end
      redirect_to :controller => 'user', :action => redirect_to_action
    end
  end
  

  def logout
    session[:user_id] = nil
    redirect_to :controller => 'user', :action => 'login'
  end


  def login
    if auto_redirect_authorized? then
      return
    end

   if not request.post? then
        return
    end

 
    @user = User.find_by(username: user_params[:username])

    if @user.nil? then
      flash[:error] = {"username": ['does not exist']}
      redirect_to :controller => 'user', :action => 'login'
    elsif !@user.authenticate(user_params[:password]) then
      flash[:error] = {"password": ["maybe incorrect"], "username": ["maybe incorrect"]}
      redirect_to :controller => 'user', :action => 'login'
    else
      session["user_id"] = @user.id
      session["username"] = @user.username
      # TODO: allow custom redirects here
      redirect_to :controller => 'user', :action => 'mainpage'
    end
  end

  def delete_account
    if kick_out_unauthorized? then
      return
    end

    if not request.delete? then
        return
    end

    SurveyResponse.where({user_id: @user.id}).each do |resp|
      Answer.delete_all({survey_response_id: resp.id})
      resp.destroy
    end

    @user.destroy

    session["user_id"] = nil
    session["username"] = nil

    redirect_to :controller => 'main', :action => 'index'

  end

  # === PARAMS ===
  def survey_params
    params.require(:survey).permit(:name)
  end


  def user_params
    params.require(:user).permit(:name, :email, :username, :password, :password_conformation)
  end

end
